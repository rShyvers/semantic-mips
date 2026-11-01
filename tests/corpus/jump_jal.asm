# jump_jal.asm — j and jal with a "return" (hardcoded j back to the known
# call-site address, since jr is out of v1 scope).
#
# Real MIPS32 jumps always execute the instruction in their delay slot (the
# one immediately following the jump) before transferring control — see
# docs/spec/SPEC-NOTES.md §9 item 1. Each jump below is therefore followed
# by a genuine no-op (`sll $zero, $zero, 0`, i.e. $zero <<= 0, into $zero)
# as its delay-slot instruction, so this file's test intent is unchanged
# under both our delay-slot-aware engine (which executes the nop
# harmlessly) and real MARS's still-no-delay-slot default config (which
# skips it harmlessly).
.text
main:
    jal  Lsub
    sll  $zero, $zero, 0
AfterCall:
    move $a0, $t0
    li   $v0, 11
    syscall
    # (no longer prints $ra's low byte here: jal's $ra legitimately diverges
    # from MARS's once a real delay-slot instruction sits between jal and
    # its continuation — see docs/spec/SPEC-NOTES.md §9 item 5. This file
    # never actually uses $ra to return (jr is out of v1 scope; see header),
    # so dropping the probe does not weaken the control-flow check below.)
    li   $v0, 10
    syscall
Lsub:
    li   $t0, 65
    j    AfterCall
    sll  $zero, $zero, 0
