import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.State
import Semantics.Instruction
import Semantics.Asm
import Semantics.Step

/-!
# MipsRun — thin "assemble and run one `.asm` program" executable

Issue #1: the VibeCheck demo (`rShyvers/VibeCheck`) lets a user paste MIPS
assembly into a web page; a small server there shells out to this binary and
renders its output. Everything this needs already exists as pure functions
(`Asm.assemble`, `initialState`, `Step.run`) — this file is only the CLI/IO
wrapper and JSON emission around them, in `DiffHarness.lean`'s style of
composing strings directly (no external JSON-library dependency; none is
present in `lake-manifest.json`'s packages to reuse).

## CLI

```
MipsRun [path.asm]
```
Reads `.asm` source from `path.asm` if given, else from stdin. Prints exactly
one JSON object to stdout and nothing else. Exit codes:
- `0` — assembled and ran to completion or to the step limit (a *program*
  runtime error, e.g. an illegal instruction, is reported as data in the
  JSON, not a nonzero exit).
- `1` — assembly failed.
- `2` — usage/IO error (unreadable file, etc.) — no JSON is printed (there is
  nothing to report: we never even got a `.asm` to try).

## Known v1 limitation: `.data` is never materialized into `State.mem`

Per the issue, this wraps `Asm.assemble`, `initialState textBase`, and `run`
**only**. `Asm.assemble` places `.data` segment words into the same
`Program` map as `.text` (word-addressed); `run`'s `lw`/`lb`/`sh`/etc.
instructions read from `State.mem` instead, which `initialState` always
starts empty. `DiffHarness.lean`'s `materialize` step exists specifically to
copy `Program`'s `.data` entries into `State.mem` before running — intentionally
not reused here, since this issue's contract pins the pipeline to exactly
those three functions. The practical effect: a submitted program that loads
from `.data` (e.g. `la $a0, msg` then `syscall 4` to print a string) will see
all-zero memory at that address rather than the declared bytes. This is a
real limitation for VibeCheck's demo UI (`.data`-based "hello world" idioms
will not work as expected) and is flagged here rather than silently worked
around, since fixing it (wiring in something like `materialize`) is outside
this issue's stated scope.
-/

/-- Convert a word to its full-width (zero-padded), lowercase hex digits,
without the `0x` prefix. Used for `illegal_instruction`/`address_error`
payloads in the JSON `halt_reason` string. -/
def toHexDigits (w : W32) : String :=
  let hexChar (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + '0'.toNat) else Char.ofNat (d - 10 + 'a'.toNat)
  let rec go : Nat → Nat → List Char → List Char
    | 0, _, acc => acc
    | fuel + 1, n, acc => go fuel (n / 16) (hexChar (n % 16) :: acc)
  String.ofList (go 8 w.toNat [])

/-- JSON-escape a string's contents (without the surrounding quotes). -/
def jsonEscape (s : String) : String :=
  let escChar (c : Char) : String :=
    match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c =>
      if c.toNat < 0x20 then
        let hexChar (d : Nat) : Char :=
          if d < 10 then Char.ofNat (d + '0'.toNat) else Char.ofNat (d - 10 + 'a'.toNat)
        let rec go : Nat → Nat → List Char → List Char
          | 0, _, acc => acc
          | fuel + 1, n, acc => go fuel (n / 16) (hexChar (n % 16) :: acc)
        s!"\\u{String.ofList (go 4 c.toNat [])}"
      else String.singleton c
  String.join (s.toList.map escChar)

/-- A JSON string literal, including surrounding quotes. -/
def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

/-- Canonical MIPS register names, indexed `0..31`, matching `Asm.lean`'s
`regTable` (the same source of truth `Asm.assemble` itself accepts register
names against) — duplicated here since `regTable` is `private` to `Asm.lean`
and so not visible across files. -/
def regNames : Array String :=
  #["zero", "at", "v0", "v1", "a0", "a1", "a2", "a3",
    "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7",
    "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7",
    "t8", "t9", "k0", "k1", "gp", "sp", "fp", "ra"]

/-- All 32 general-purpose registers of `s`, as a JSON object, canonical
names to unsigned decimal values. -/
def registersJson (s : State) : String :=
  let pairs := (List.range 32).map (fun i =>
    s!"{jsonStr (regNames[i]!)}: {(s.regs.getD i 0#32).toNat}")
  "{" ++ String.intercalate ", " pairs ++ "}"

/-- Render an `AsmError` as the human-readable string the `error` field
carries when assembly fails, including the 1-based source line number. -/
def renderAsmError (e : AsmError) : String :=
  match e with
  | .unknownMnemonic msg line => s!"unknown mnemonic: {msg} (line {line})"
  | .badRegister msg line => s!"bad register: {msg} (line {line})"
  | .undefinedLabel msg line => s!"undefined label: {msg} (line {line})"
  | .badImmediate msg line => s!"bad immediate: {msg} (line {line})"
  | .badDirective msg line => s!"bad directive: {msg} (line {line})"
  | .badOperand msg line => s!"bad operand: {msg} (line {line})"
  | .duplicateLabel msg line => s!"duplicate label: {msg} (line {line})"

/-- Render a `HaltReason` as the `halt_reason` string: the two payload-carrying
cases append the word/address in hex, per the issue's output contract.

`branchInDelaySlot` is a MipsRun-specific extension beyond the issue's
enumerated `halt_reason` list (`"exit" | "illegal_instruction" |
"address_error" | "arithmetic_overflow"`): the issue was written before the
real MIPS32 branch-delay-slot work (and its `HaltReason.branchInDelaySlot`
constructor) landed. It carries no payload, so — like `exit`/
`arithmeticOverflow` — it renders as a plain string with no hex suffix. -/
def renderHaltReason (r : HaltReason) : String :=
  match r with
  | .exit => "exit"
  | .illegalInstruction w => s!"illegal_instruction:0x{toHexDigits w}"
  | .addressError a => s!"address_error:0x{toHexDigits a}"
  | .arithmeticOverflow => "arithmetic_overflow"
  | .branchInDelaySlot => "branch_in_delay_slot"

/-- The full success-path JSON object (`assembled: true`), for either a
`halted` or `limitReached` `RunResult`. -/
def renderRunResult (r : RunResult) : String :=
  let (halted, haltReasonJson, steps, s) :=
    match r with
    | .halted reason s steps => (true, jsonStr (renderHaltReason reason), steps, s)
    | .limitReached s steps => (false, "null", steps, s)
  "{\"assembled\": true, " ++
  s!"\"halted\": {halted}, " ++
  s!"\"halt_reason\": {haltReasonJson}, " ++
  s!"\"steps\": {steps}, " ++
  s!"\"output\": {jsonStr s.out}, " ++
  s!"\"registers\": {registersJson s}, " ++
  "\"error\": null}"

/-- The failure-path JSON object (`assembled: false`): every field besides
`assembled`/`error` is `null`, per the issue's field rules. -/
def renderAsmFailure (e : AsmError) : String :=
  "{\"assembled\": false, \"halted\": null, \"halt_reason\": null, " ++
  "\"steps\": null, \"output\": null, \"registers\": null, " ++
  s!"\"error\": {jsonStr (renderAsmError e)}}"

/-- Read the `.asm` source: from the file at `path` if given, else from
stdin. `Except.error` carries a human message for a `2`-exit usage/IO error
(no JSON is printed in that case — there is no program to report on). -/
def readSource (path : Option String) : IO (Except String String) := do
  try
    match path with
    | some p => pure (Except.ok (← IO.FS.readFile p))
    | none => pure (Except.ok (← (← IO.getStdin).readToEnd))
  catch e => pure (Except.error (toString e))

def main (args : List String) : IO UInt32 := do
  match ← readSource args.head? with
  | .error msg =>
    IO.eprintln s!"MipsRun: {msg}"
    return 2
  | .ok src =>
    match assemble src with
    | .error e =>
      IO.println (renderAsmFailure e)
      return 1
    | .ok prog =>
      let maxSteps : Nat := 1000000
      let result := run prog (initialState textBase) maxSteps
      IO.println (renderRunResult result)
      return 0

-- ====================================================================
-- ## In-file tests (DESIGN.md §5 / CLAUDE.md §5)
--
-- `#guard`-checked, hand-crafted `.asm` programs (inline string literals,
-- in the style of `DiffHarness.lean`'s embedded corpus copies) exercising
-- the same `assemble`/`run` pipeline `main` drives, covering the four
-- cases the issue calls out: a clean exit with output, an assembly error,
-- an illegal-instruction halt, and the step-limit-exhausted case. These
-- check the underlying `RunResult`/`AsmResult` classification (what
-- `renderRunResult`/`renderAsmFailure` then render into JSON); the actual
-- rendered JSON shape for each of these four cases was additionally
-- eyeballed against the issue's example by running the built binary
-- directly (see the task report — not reproducible inside `#guard`, since
-- that only sees pure values, not stdout/exit codes).
-- ====================================================================

section GoldenTests

/-- Clean exit with non-empty output: print `$a0` as an int (syscall 1),
then exit (syscall 10). -/
private def cleanExitSrc : String :=
"main:\n" ++
"    li   $v0, 1\n" ++
"    li   $a0, 42\n" ++
"    syscall\n" ++
"    li   $v0, 10\n" ++
"    syscall\n"

private def cleanExitResult : RunResult :=
  match assemble cleanExitSrc with
  | .ok prog => run prog (initialState textBase) 1000000
  | .error _ => .limitReached (initialState textBase) 0 -- unreachable: assembles fine

#guard (match cleanExitResult with | .halted .exit _ _ => true | _ => false)
#guard (match cleanExitResult with | .halted .exit s _ => s.out == "42" | _ => false)

/-- Not MIPS at all — `assemble` must reject it with an error, not throw. -/
private def notMipsSrc : String := "not mips at all"

#guard (match assemble notMipsSrc with | .error _ => true | .ok _ => false)

/-- Illegal instruction halt: an unsupported syscall service number (99)
is, per `Step.execInstr`, reported the same way as any other
undecodable-in-context word. -/
private def illegalInstrSrc : String :=
"main:\n" ++
"    li   $v0, 99\n" ++
"    syscall\n"

private def illegalInstrResult : RunResult :=
  match assemble illegalInstrSrc with
  | .ok prog => run prog (initialState textBase) 1000000
  | .error _ => .limitReached (initialState textBase) 0 -- unreachable: assembles fine

#guard (match illegalInstrResult with | .halted (.illegalInstruction _) _ _ => true | _ => false)

/-- Step-limit-exhausted: an unconditional self-jump never halts, so a small
fuel budget is exhausted (kept small here for test speed; `main` itself
uses the full `1_000_000`-step budget).

Includes an explicit `nop` delay-slot instruction after the `j`: real MIPS32
branches/jumps never transfer control immediately (SPEC-NOTES §9 item 1) --
`j main`'s own step falls through to `pc + 4` and only *schedules* `main` as
the target (`State.pendingBranch`), which is committed by whichever
instruction retires next. Without a delay-slot instruction physically
present at `pc + 4`, that next fetch has nothing to read (this program's
only assembled word is the `j` itself) and the run halts on `addressError`
after 2 steps instead of ever reaching the step limit. The `nop` fills that
slot so the loop is genuinely infinite (2 steps per iteration: the `j`, then
its delay slot, which is where the jump actually lands), matching this
test's intent of exercising the step-limit/`"halted": false` path -- it
still runs for exactly `maxSteps` steps since it never halts on its own. -/
private def infiniteLoopSrc : String :=
"main:\n" ++
"    j main\n" ++
"    nop\n"

private def infiniteLoopResult : RunResult :=
  match assemble infiniteLoopSrc with
  | .ok prog => run prog (initialState textBase) 50
  | .error _ => .halted .exit (initialState textBase) 0 -- unreachable: assembles fine

#guard (match infiniteLoopResult with | .limitReached _ steps => steps == 50 | _ => false)

end GoldenTests
