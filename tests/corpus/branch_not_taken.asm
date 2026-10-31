# branch_not_taken.asm — beq/bne/blez/bgtz, all four conditions FALSE (not taken).
.text
main:
    li   $t0, 5
    li   $t1, 6
    li   $t2, 1
    beq  $t0, $t1, Lbeq   # 5 != 6 -> not taken
    li   $t2, 0
Lbeq:
    li   $t3, 3
    li   $t4, 3
    li   $t5, 1
    bne  $t3, $t4, Lbne   # 3 == 3 -> not taken
    li   $t5, 0
Lbne:
    li   $t6, 5
    li   $t7, 1
    blez $t6, Lblez       # 5 > 0 -> not taken
    li   $t7, 0
Lblez:
    li   $t8, -3
    li   $t9, 1
    bgtz $t8, Lbgtz       # -3 <= 0 -> not taken
    li   $t9, 0
Lbgtz:
    move $a0, $t2
    li   $v0, 11
    syscall
    move $a0, $t5
    li   $v0, 11
    syscall
    move $a0, $t7
    li   $v0, 11
    syscall
    move $a0, $t9
    li   $v0, 11
    syscall
    li   $v0, 10
    syscall
