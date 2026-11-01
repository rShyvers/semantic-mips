# div_pow2_shift_correct.asm — $a0 / 4, signed, truncating toward zero, via
# shift — but with the standard bias correction for negative dividends
# (add divisor-1 before shifting) that div_pow2_shift_buggy.asm is missing.
# Claimed equivalent to div_pow2_base.asm for every 32-bit input.
#
# Real MIPS32 branches/jumps always execute the instruction in their delay
# slot before transferring control (docs/spec/SPEC-NOTES.md §9 item 1), so
# `beq` and `j` below are each followed by a genuine no-op
# (`sll $zero, $zero, 0`) as their delay-slot instruction. This leaves the
# branch targets (and therefore the biasing `addi`'s being skipped exactly
# when $a0 >= 0) unchanged: the nop after `beq` executes harmlessly then
# control still lands on `Lnonneg` when taken, and the nop after `j`
# executes harmlessly then control still lands on `Lend`.
.text
main:
    slt  $t1, $a0, $zero     # t1 = 1 if $a0 < 0, else 0
    beq  $t1, $zero, Lnonneg
    sll  $zero, $zero, 0
    addi $t2, $a0, 3         # bias: divisor - 1, only needed when negative
    sra  $t9, $t2, 2
    j    Lend
    sll  $zero, $zero, 0
Lnonneg:
    sra  $t9, $a0, 2
Lend:
    li   $v0, 10
    syscall
