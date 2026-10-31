# i_imm.asm — addi, andi, ori, xori, lui.
.text
main:
    li    $t0, 10
    addi  $t1, $t0, 5      # 15
    andi  $t2, $t0, 0x7    # 10 & 7 = 2
    ori   $t3, $t0, 0x5    # 10 | 5 = 15
    xori  $t4, $t0, 0x3    # 10 ^ 3 = 9
    lui   $t5, 0x1         # 0x00010000
    srl   $t6, $t5, 16     # 1
    andi  $a0, $t1, 0x7f
    li    $v0, 11
    syscall
    andi  $a0, $t2, 0x7f
    li    $v0, 11
    syscall
    andi  $a0, $t3, 0x7f
    li    $v0, 11
    syscall
    andi  $a0, $t4, 0x7f
    li    $v0, 11
    syscall
    andi  $a0, $t6, 0x7f
    li    $v0, 11
    syscall
    li    $v0, 10
    syscall
