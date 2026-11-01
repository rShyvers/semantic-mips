# mod_pow2_mask_correct.asm — $a0 % 4, signed, via shift + multiply-back:
# rem = $a0 - ($a0 / 4) * 4, where the quotient is the same bias-corrected
# truncating shift as div_pow2_shift_correct.asm. Claimed equivalent to
# mod_pow2_base.asm for every 32-bit input.
#
# Real MIPS32 branches/jumps always execute the instruction in their delay
# slot before transferring control (docs/spec/SPEC-NOTES.md §9 item 1), so
# `beq` and `j` below are each followed by a genuine no-op
# (`sll $zero, $zero, 0`) as their delay-slot instruction. This leaves the
# branch targets (and therefore the biasing `addi`'s being skipped exactly
# when $a0 >= 0) unchanged: the nop after `beq` executes harmlessly then
# control still lands on `Lnonneg` when taken, and the nop after `j`
# executes harmlessly then control still lands on `Lcomputed`.
.text
main:
    slt  $t1, $a0, $zero     # t1 = 1 if $a0 < 0, else 0
    beq  $t1, $zero, Lnonneg
    sll  $zero, $zero, 0
    addi $t2, $a0, 3
    sra  $t4, $t2, 2
    j    Lcomputed
    sll  $zero, $zero, 0
Lnonneg:
    sra  $t4, $a0, 2
Lcomputed:
    sll  $t5, $t4, 2         # t5 = quotient * 4
    sub  $t9, $a0, $t5       # t9 = $a0 - quotient*4 = remainder
    li   $v0, 10
    syscall
