import MipsSim.Word
import MipsSim.Types

/-!
# Instruction — the v1 MIPS instruction set, decode, and encode

Wave 1 module (DESIGN.md §4, worker C). Depends only on `Word` and `Types`
(foundation, read-only). Ground truth for every encoding below is
`docs/spec/INSTRUCTION-REF.md`.

All instruction variants carry their **raw** field values as `W32`s (not yet
sign/zero-extended, not yet interpreted as signed shift amounts, etc.) — the
Wave 2 `Step` worker is responsible for applying `signExt16` / `zeroExt16` /
`.toNat` / `.toInt` as each instruction's semantics require. This keeps
`decode`/`encode` a pure, total, reversible bit-layout transformation with no
semantic interpretation baked in.

Field-shape summary (see each constructor's docstring for details):
- R-type reg/reg/reg (`rs rt rd`): `add addu sub subu and or xor nor slt sltu`.
- R-type shift (`rd rt shamt`): `sll srl sra` — note `rs` is unused/ignored.
- R-type mult/div (`rs rt`): `mult multu div divu` — `rd`/`shamt` unused.
- R-type move (`rd`): `mflo mfhi` — `rs`/`rt`/`shamt` unused.
- I-type arith/logic (`rs rt imm`): `addi addiu slti sltiu andi ori xori`.
- I-type `lui` (`rt imm`): `rs` is unused/fixed 0.
- I-type load/store (`rs rt imm`): `lw sw lb lbu lh lhu sh` — `rs` is the base
  register, `rt` is the destination (loads) or source (stores) register,
  `imm` is the raw 16-bit offset field (not yet sign-extended).
- I-type branch reg/reg (`rs rt imm`): `beq bne`.
- I-type branch reg-only (`rs imm`): `blez bgtz` — `rt` is unused/fixed 0.
- J-type (`target`): `j jal` — raw 26-bit target field (not yet shifted/combined
  with `PC_next`'s top 4 bits; that composition is `Step`'s job).
- No fields: `syscall` — the syscall *number* lives in `$v0` at execution
  time (MARS convention), so the instruction word carries no operand data
  beyond `opcode=0`/`funct=0x0c`.
-/

/-- The full v1 machine-instruction set (24 real instructions plus `syscall`).
Each constructor's fields are the **raw** bit-field values extracted from the
32-bit encoding — see the module docstring for which fields each variant
carries and INSTRUCTION-REF for the exact bit layout and semantics. -/
inductive Instruction where
  -- R-type reg/reg/reg
  /-- `$rd = $rs + $rt`, signed; traps on overflow (opcode 0, funct 0x20). -/
  | add  (rs rt rd : W32)
  /-- `$rd = $rs + $rt`, wraps (opcode 0, funct 0x21). -/
  | addu (rs rt rd : W32)
  /-- `$rd = $rs - $rt`, signed; traps on overflow (opcode 0, funct 0x22). -/
  | sub  (rs rt rd : W32)
  /-- `$rd = $rs - $rt`, wraps (opcode 0, funct 0x23). -/
  | subu (rs rt rd : W32)
  /-- `$rd = $rs & $rt` (opcode 0, funct 0x24). -/
  | and  (rs rt rd : W32)
  /-- `$rd = $rs | $rt` (opcode 0, funct 0x25). -/
  | or   (rs rt rd : W32)
  /-- `$rd = $rs ^ $rt` (opcode 0, funct 0x26). -/
  | xor  (rs rt rd : W32)
  /-- `$rd = ~($rs | $rt)` (opcode 0, funct 0x27). -/
  | nor  (rs rt rd : W32)
  /-- `$rd = ($rs < $rt) ? 1 : 0`, signed (opcode 0, funct 0x2a). -/
  | slt  (rs rt rd : W32)
  /-- `$rd = ($rs <u $rt) ? 1 : 0`, unsigned (opcode 0, funct 0x2b). -/
  | sltu (rs rt rd : W32)
  -- R-type shift (rs unused)
  /-- `$rd = $rt << shamt`, logical (opcode 0, funct 0x00). -/
  | sll  (rd rt shamt : W32)
  /-- `$rd = $rt >> shamt`, logical/zero-fill (opcode 0, funct 0x02). -/
  | srl  (rd rt shamt : W32)
  /-- `$rd = $rt >> shamt`, arithmetic/sign-fill (opcode 0, funct 0x03). -/
  | sra  (rd rt shamt : W32)
  -- R-type mult/div (rd, shamt unused)
  /-- `{hi,lo} = $rs * $rt`, signed 64-bit (opcode 0, funct 0x18). -/
  | mult   (rs rt : W32)
  /-- `{hi,lo} = $rs * $rt`, unsigned 64-bit (opcode 0, funct 0x19). -/
  | multu  (rs rt : W32)
  /-- `lo = $rs / $rt; hi = $rs % $rt`, signed (opcode 0, funct 0x1a). -/
  | div    (rs rt : W32)
  /-- `lo = $rs / $rt; hi = $rs % $rt`, unsigned (opcode 0, funct 0x1b). -/
  | divu   (rs rt : W32)
  -- R-type move (rs, rt, shamt unused)
  /-- `$rd = lo` (opcode 0, funct 0x12). -/
  | mflo (rd : W32)
  /-- `$rd = hi` (opcode 0, funct 0x10). -/
  | mfhi (rd : W32)
  -- I-type arith/logic
  /-- `$rt = $rs + sext16(imm)`, traps on overflow (opcode 0x08). -/
  | addi  (rs rt imm : W32)
  /-- `$rt = $rs + sext16(imm)`, wraps (opcode 0x09). -/
  | addiu (rs rt imm : W32)
  /-- `$rt = ($rs < sext16(imm)) ? 1 : 0`, signed (opcode 0x0a). -/
  | slti  (rs rt imm : W32)
  /-- `$rt = ($rs <u sext16(imm)) ? 1 : 0` (opcode 0x0b). -/
  | sltiu (rs rt imm : W32)
  /-- `$rt = $rs & zext16(imm)` (opcode 0x0c). -/
  | andi  (rs rt imm : W32)
  /-- `$rt = $rs | zext16(imm)` (opcode 0x0d). -/
  | ori   (rs rt imm : W32)
  /-- `$rt = $rs ^ zext16(imm)` (opcode 0x0e). -/
  | xori  (rs rt imm : W32)
  -- I-type lui (rs unused/fixed 0)
  /-- `$rt = imm << 16` (opcode 0x0f). -/
  | lui   (rt imm : W32)
  -- I-type load/store: rs = base, rt = dest/src, imm = raw offset field
  /-- `$rt = MEM32[$rs + offset]`, word-aligned (opcode 0x23). -/
  | lw  (rs rt imm : W32)
  /-- `MEM32[$rs + offset] = $rt`, word-aligned (opcode 0x2b). -/
  | sw  (rs rt imm : W32)
  /-- `$rt = sext8(MEM8[$rs + offset])` (opcode 0x20). -/
  | lb  (rs rt imm : W32)
  /-- `$rt = zext8(MEM8[$rs + offset])` (opcode 0x24). -/
  | lbu (rs rt imm : W32)
  /-- `$rt = sext16(MEM16[$rs + offset])`, halfword-aligned (opcode 0x21). -/
  | lh  (rs rt imm : W32)
  /-- `$rt = zext16(MEM16[$rs + offset])`, halfword-aligned (opcode 0x25). -/
  | lhu (rs rt imm : W32)
  /-- `MEM16[$rs + offset] = $rt[15:0]`, halfword-aligned (opcode 0x29). -/
  | sh  (rs rt imm : W32)
  -- I-type branch reg/reg
  /-- `if $rs == $rt then PC = PC_next + (sext16(imm) << 2)` (opcode 0x04). -/
  | beq (rs rt imm : W32)
  /-- `if $rs != $rt then PC = PC_next + (sext16(imm) << 2)` (opcode 0x05). -/
  | bne (rs rt imm : W32)
  -- I-type branch reg-only (rt unused/fixed 0)
  /-- `if $rs <= 0 then PC = PC_next + (sext16(imm) << 2)` (opcode 0x06). -/
  | blez (rs imm : W32)
  /-- `if $rs > 0 then PC = PC_next + (sext16(imm) << 2)` (opcode 0x07). -/
  | bgtz (rs imm : W32)
  -- J-type
  /-- `PC = (PC_next & 0xF0000000) | (target << 2)` (opcode 0x02). -/
  | j   (target : W32)
  /-- `$ra = PC_next; PC = (PC_next & 0xF0000000) | (target << 2)` (opcode 0x03). -/
  | jal (target : W32)
  -- syscall (no fields; the syscall number lives in $v0 at execution time)
  /-- Dispatch on `$v0` (opcode 0, funct 0x0c); MARS syscalls 1/4/10/11 in v1 scope. -/
  | syscall
  deriving Repr, DecidableEq

/-- Extract the 6-bit opcode field (bits 31..26), zero-extended to a `W32`. -/
private def opcodeOf (w : W32) : W32 := (w.extractLsb 31 26).zeroExtend 32

/-- Extract the 5-bit `rs` field (bits 25..21), zero-extended to a `W32`. -/
private def rsOf (w : W32) : W32 := (w.extractLsb 25 21).zeroExtend 32

/-- Extract the 5-bit `rt` field (bits 20..16), zero-extended to a `W32`. -/
private def rtOf (w : W32) : W32 := (w.extractLsb 20 16).zeroExtend 32

/-- Extract the 5-bit `rd` field (bits 15..11), zero-extended to a `W32`. -/
private def rdOf (w : W32) : W32 := (w.extractLsb 15 11).zeroExtend 32

/-- Extract the 5-bit `shamt` field (bits 10..6), zero-extended to a `W32`. -/
private def shamtOf (w : W32) : W32 := (w.extractLsb 10 6).zeroExtend 32

/-- Extract the 6-bit `funct` field (bits 5..0), zero-extended to a `W32`. -/
private def functOf (w : W32) : W32 := (w.extractLsb 5 0).zeroExtend 32

/-- Extract the raw 16-bit immediate/offset field (bits 15..0), zero-extended
to a `W32` with no sign interpretation applied. -/
private def immOf (w : W32) : W32 := (w.extractLsb 15 0).zeroExtend 32

/-- Extract the raw 26-bit jump-target field (bits 25..0), zero-extended to a `W32`. -/
private def targetOf (w : W32) : W32 := (w.extractLsb 25 0).zeroExtend 32

/-- Decode a raw 32-bit instruction word into an `Instruction`, or `none` if
the opcode/funct combination is not in the v1 instruction set. Ground truth:
`docs/spec/INSTRUCTION-REF.md`. -/
def decode (w : W32) : Option Instruction :=
  let rs := rsOf w
  let rt := rtOf w
  let rd := rdOf w
  let shamt := shamtOf w
  let imm := immOf w
  let target := targetOf w
  match (opcodeOf w).toNat with
  | 0x00 =>
    match (functOf w).toNat with
    | 0x20 => some (.add rs rt rd)
    | 0x21 => some (.addu rs rt rd)
    | 0x22 => some (.sub rs rt rd)
    | 0x23 => some (.subu rs rt rd)
    | 0x24 => some (.and rs rt rd)
    | 0x25 => some (.or rs rt rd)
    | 0x26 => some (.xor rs rt rd)
    | 0x27 => some (.nor rs rt rd)
    | 0x2a => some (.slt rs rt rd)
    | 0x2b => some (.sltu rs rt rd)
    | 0x00 => some (.sll rd rt shamt)
    | 0x02 => some (.srl rd rt shamt)
    | 0x03 => some (.sra rd rt shamt)
    | 0x18 => some (.mult rs rt)
    | 0x19 => some (.multu rs rt)
    | 0x1a => some (.div rs rt)
    | 0x1b => some (.divu rs rt)
    | 0x12 => some (.mflo rd)
    | 0x10 => some (.mfhi rd)
    | 0x0c => some .syscall
    | _ => none
  | 0x08 => some (.addi rs rt imm)
  | 0x09 => some (.addiu rs rt imm)
  | 0x0a => some (.slti rs rt imm)
  | 0x0b => some (.sltiu rs rt imm)
  | 0x0c => some (.andi rs rt imm)
  | 0x0d => some (.ori rs rt imm)
  | 0x0e => some (.xori rs rt imm)
  | 0x0f => some (.lui rt imm)
  | 0x23 => some (.lw rs rt imm)
  | 0x2b => some (.sw rs rt imm)
  | 0x20 => some (.lb rs rt imm)
  | 0x24 => some (.lbu rs rt imm)
  | 0x21 => some (.lh rs rt imm)
  | 0x25 => some (.lhu rs rt imm)
  | 0x29 => some (.sh rs rt imm)
  | 0x04 => some (.beq rs rt imm)
  | 0x05 => some (.bne rs rt imm)
  | 0x06 => some (.blez rs imm)
  | 0x07 => some (.bgtz rs imm)
  | 0x02 => some (.j target)
  | 0x03 => some (.jal target)
  | _ => none

/-- Encode an `Instruction` back into its raw 32-bit word. Inverse of `decode`
on the v1 instruction set. -/
def encode (i : Instruction) : W32 :=
  match i with
  | .add  rs rt rd => mkRT rs rt rd 0#32 0x20#32
  | .addu rs rt rd => mkRT rs rt rd 0#32 0x21#32
  | .sub  rs rt rd => mkRT rs rt rd 0#32 0x22#32
  | .subu rs rt rd => mkRT rs rt rd 0#32 0x23#32
  | .and  rs rt rd => mkRT rs rt rd 0#32 0x24#32
  | .or   rs rt rd => mkRT rs rt rd 0#32 0x25#32
  | .xor  rs rt rd => mkRT rs rt rd 0#32 0x26#32
  | .nor  rs rt rd => mkRT rs rt rd 0#32 0x27#32
  | .slt  rs rt rd => mkRT rs rt rd 0#32 0x2a#32
  | .sltu rs rt rd => mkRT rs rt rd 0#32 0x2b#32
  | .sll  rd rt shamt => mkRT 0#32 rt rd shamt 0x00#32
  | .srl  rd rt shamt => mkRT 0#32 rt rd shamt 0x02#32
  | .sra  rd rt shamt => mkRT 0#32 rt rd shamt 0x03#32
  | .mult  rs rt => mkRT rs rt 0#32 0#32 0x18#32
  | .multu rs rt => mkRT rs rt 0#32 0#32 0x19#32
  | .div   rs rt => mkRT rs rt 0#32 0#32 0x1a#32
  | .divu  rs rt => mkRT rs rt 0#32 0#32 0x1b#32
  | .mflo rd => mkRT 0#32 0#32 rd 0#32 0x12#32
  | .mfhi rd => mkRT 0#32 0#32 rd 0#32 0x10#32
  | .addi  rs rt imm => mkIT 0x08#32 rs rt imm
  | .addiu rs rt imm => mkIT 0x09#32 rs rt imm
  | .slti  rs rt imm => mkIT 0x0a#32 rs rt imm
  | .sltiu rs rt imm => mkIT 0x0b#32 rs rt imm
  | .andi  rs rt imm => mkIT 0x0c#32 rs rt imm
  | .ori   rs rt imm => mkIT 0x0d#32 rs rt imm
  | .xori  rs rt imm => mkIT 0x0e#32 rs rt imm
  | .lui   rt imm    => mkIT 0x0f#32 0#32 rt imm
  | .lw rs rt imm => mkIT 0x23#32 rs rt imm
  | .sw rs rt imm => mkIT 0x2b#32 rs rt imm
  | .lb rs rt imm => mkIT 0x20#32 rs rt imm
  | .lbu rs rt imm => mkIT 0x24#32 rs rt imm
  | .lh rs rt imm => mkIT 0x21#32 rs rt imm
  | .lhu rs rt imm => mkIT 0x25#32 rs rt imm
  | .sh rs rt imm => mkIT 0x29#32 rs rt imm
  | .beq rs rt imm => mkIT 0x04#32 rs rt imm
  | .bne rs rt imm => mkIT 0x05#32 rs rt imm
  | .blez rs imm => mkIT 0x06#32 rs 0#32 imm
  | .bgtz rs imm => mkIT 0x07#32 rs 0#32 imm
  | .j   target => (0x02#32 <<< 26) ||| mkJT target
  | .jal target => (0x03#32 <<< 26) ||| mkJT target
  | .syscall => mkRT 0#32 0#32 0#32 0#32 0x0c#32

-- ## Tests

-- Each v1 instruction: hand-computed word (from INSTRUCTION-REF encodings,
-- distinct nontrivial field values) decodes to the expected variant.

-- R-type reg/reg/reg: rs=29, rt=8, rd=3
example : decode (mkRT 29#32 8#32 3#32 0#32 0x20#32) = some (.add 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x21#32) = some (.addu 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x22#32) = some (.sub 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x23#32) = some (.subu 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x24#32) = some (.and 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x25#32) = some (.or 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x26#32) = some (.xor 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x27#32) = some (.nor 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x2a#32) = some (.slt 29#32 8#32 3#32) := by decide
example : decode (mkRT 29#32 8#32 3#32 0#32 0x2b#32) = some (.sltu 29#32 8#32 3#32) := by decide

-- R-type shift: rd=3, rt=8, shamt=5 (rs unused/0)
example : decode (mkRT 0#32 8#32 3#32 5#32 0x00#32) = some (.sll 3#32 8#32 5#32) := by decide
example : decode (mkRT 0#32 8#32 3#32 5#32 0x02#32) = some (.srl 3#32 8#32 5#32) := by decide
example : decode (mkRT 0#32 8#32 3#32 5#32 0x03#32) = some (.sra 3#32 8#32 5#32) := by decide

-- R-type mult/div: rs=29, rt=8
example : decode (mkRT 29#32 8#32 0#32 0#32 0x18#32) = some (.mult 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x19#32) = some (.multu 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x1a#32) = some (.div 29#32 8#32) := by decide
example : decode (mkRT 29#32 8#32 0#32 0#32 0x1b#32) = some (.divu 29#32 8#32) := by decide

-- R-type move: rd=3
example : decode (mkRT 0#32 0#32 3#32 0#32 0x12#32) = some (.mflo 3#32) := by decide
example : decode (mkRT 0#32 0#32 3#32 0#32 0x10#32) = some (.mfhi 3#32) := by decide

-- syscall: opcode 0, funct 0x0c, all other fields 0
example : decode (mkRT 0#32 0#32 0#32 0#32 0x0c#32) = some .syscall := by decide

-- I-type arith/logic: rs=29, rt=8, imm=0x1234
example : decode (mkIT 0x08#32 29#32 8#32 0x1234#32) = some (.addi 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x09#32 29#32 8#32 0x1234#32) = some (.addiu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0a#32 29#32 8#32 0x1234#32) = some (.slti 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0b#32 29#32 8#32 0x1234#32) = some (.sltiu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0c#32 29#32 8#32 0x1234#32) = some (.andi 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0d#32 29#32 8#32 0x1234#32) = some (.ori 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x0e#32 29#32 8#32 0x1234#32) = some (.xori 29#32 8#32 0x1234#32) := by decide

-- lui: rt=8, imm=0x1234 (rs fixed 0)
example : decode (mkIT 0x0f#32 0#32 8#32 0x1234#32) = some (.lui 8#32 0x1234#32) := by decide

-- load/store: rs=29 (base), rt=8 (dest/src), imm=0x1234 (offset)
example : decode (mkIT 0x23#32 29#32 8#32 0x1234#32) = some (.lw 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x2b#32 29#32 8#32 0x1234#32) = some (.sw 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x20#32 29#32 8#32 0x1234#32) = some (.lb 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x24#32 29#32 8#32 0x1234#32) = some (.lbu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x21#32 29#32 8#32 0x1234#32) = some (.lh 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x25#32 29#32 8#32 0x1234#32) = some (.lhu 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x29#32 29#32 8#32 0x1234#32) = some (.sh 29#32 8#32 0x1234#32) := by decide

-- branch reg/reg: rs=29, rt=8, imm=0x1234
example : decode (mkIT 0x04#32 29#32 8#32 0x1234#32) = some (.beq 29#32 8#32 0x1234#32) := by decide
example : decode (mkIT 0x05#32 29#32 8#32 0x1234#32) = some (.bne 29#32 8#32 0x1234#32) := by decide

-- branch reg-only: rs=29, imm=0x1234 (rt fixed 0)
example : decode (mkIT 0x06#32 29#32 0#32 0x1234#32) = some (.blez 29#32 0x1234#32) := by decide
example : decode (mkIT 0x07#32 29#32 0#32 0x1234#32) = some (.bgtz 29#32 0x1234#32) := by decide

-- J-type: target = 0x3ffffff (all 26 bits)
example : decode ((0x02#32 <<< 26) ||| mkJT 0x3ffffff#32) = some (.j 0x3ffffff#32) := by decide
example : decode ((0x03#32 <<< 26) ||| mkJT 0x3ffffff#32) = some (.jal 0x3ffffff#32) := by decide

-- `encode ∘ decode` round-trips, spanning R / I / J / branch / syscall
example : encode (.add 29#32 8#32 3#32) = mkRT 29#32 8#32 3#32 0#32 0x20#32 := by decide
example : encode (.lw 29#32 8#32 0x1234#32) = mkIT 0x23#32 29#32 8#32 0x1234#32 := by decide
example : encode (.beq 29#32 8#32 0x1234#32) = mkIT 0x04#32 29#32 8#32 0x1234#32 := by decide
example : encode (.j 0x3ffffff#32) = (0x02#32 <<< 26) ||| mkJT 0x3ffffff#32 := by decide
example : encode .syscall = mkRT 0#32 0#32 0#32 0#32 0x0c#32 := by decide
example : encode (.sll 3#32 8#32 5#32) = mkRT 0#32 8#32 3#32 5#32 0x00#32 := by decide

-- unknown opcodes → none
#guard decode (mkIT 0x01#32 0#32 0#32 0#32) = none  -- coprocessor-1, unimplemented
#guard decode (mkIT 0x11#32 0#32 0#32 0#32) = none
#guard decode (mkIT 0x16#32 0#32 0#32 0#32) = none
#guard decode (mkIT 0x17#32 0#32 0#32 0#32) = none
#guard decode (mkIT 0x1c#32 0#32 0#32 0#32) = none
#guard decode (mkIT 0x1d#32 0#32 0#32 0#32) = none

-- unknown functs under opcode 0 → none
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x01#32) = none
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x3f#32) = none

-- a few key decodes
#guard decode (mkRT 29#32 8#32 3#32 0#32 0x20#32) = some (.add 29#32 8#32 3#32)
#guard decode (mkIT 0x23#32 29#32 8#32 0x1234#32) = some (.lw 29#32 8#32 0x1234#32)
#guard decode ((0x02#32 <<< 26) ||| mkJT 0x3ffffff#32) = some (.j 0x3ffffff#32)
#guard decode (mkRT 0#32 0#32 0#32 0#32 0x0c#32) = some .syscall
