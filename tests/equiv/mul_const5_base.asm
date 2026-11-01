# mul_const5_base.asm — $t9 = $a0 * 5, direct multiply.
.text
main:
    li   $t0, 5
    mult $a0, $t0
    mflo $t9
    li   $v0, 10
    syscall
