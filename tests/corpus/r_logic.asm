# r_logic.asm — and, or, xor, nor, slt.
.text
main:
    li   $t0, 0x6a        # 0110 1010
    li   $t1, 0x3c        # 0011 1100
    and  $t2, $t0, $t1    # 0010 1000 = 0x28
    or   $t3, $t0, $t1    # 0111 1110 = 0x7e
    xor  $t4, $t0, $t1    # 0101 0110 = 0x56
    nor  $t5, $t0, $t1    # ~0x7e = 0xffffff81
    slt  $t6, $t1, $t0    # 0x3c < 0x6a -> 1
    andi $a0, $t2, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t3, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t4, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t5, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t6, 0x7f
    li   $v0, 11
    syscall
    li   $v0, 10
    syscall
