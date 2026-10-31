# addi_neg.asm — addi with a negative immediate, and slt/sltu disagreement
# on a value with the sign bit set (unsigned vs signed comparison).
.text
main:
    li   $t0, 10
    addi $t1, $t0, -3     # 7
    li   $t2, 0xffffffff  # -1 signed / huge unsigned
    li   $t3, 1
    slt  $t4, $t2, $t3    # signed: -1 < 1 -> 1
    sltu $t5, $t2, $t3    # unsigned: 0xffffffff < 1 -> 0
    andi $a0, $t1, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t4, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t5, 0x7f
    li   $v0, 11
    syscall
    li   $v0, 10
    syscall
