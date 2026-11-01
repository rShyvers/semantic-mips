# div_pow2_shift_correct.asm — $a0 / 4, signed, truncating toward zero, via
# shift — but with the standard bias correction for negative dividends
# (add divisor-1 before shifting) that div_pow2_shift_buggy.asm is missing.
# Claimed equivalent to div_pow2_base.asm for every 32-bit input.
.text
main:
    slt  $t1, $a0, $zero     # t1 = 1 if $a0 < 0, else 0
    beq  $t1, $zero, Lnonneg
    addi $t2, $a0, 3         # bias: divisor - 1, only needed when negative
    sra  $t9, $t2, 2
    j    Lend
Lnonneg:
    sra  $t9, $a0, 2
Lend:
    li   $v0, 10
    syscall
