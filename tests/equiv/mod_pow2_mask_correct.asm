# mod_pow2_mask_correct.asm — $a0 % 4, signed, via shift + multiply-back:
# rem = $a0 - ($a0 / 4) * 4, where the quotient is the same bias-corrected
# truncating shift as div_pow2_shift_correct.asm. Claimed equivalent to
# mod_pow2_base.asm for every 32-bit input.
.text
main:
    slt  $t1, $a0, $zero     # t1 = 1 if $a0 < 0, else 0
    beq  $t1, $zero, Lnonneg
    addi $t2, $a0, 3
    sra  $t4, $t2, 2
    j    Lcomputed
Lnonneg:
    sra  $t4, $a0, 2
Lcomputed:
    sll  $t5, $t4, 2         # t5 = quotient * 4
    sub  $t9, $a0, $t5       # t9 = $a0 - quotient*4 = remainder
    li   $v0, 10
    syscall
