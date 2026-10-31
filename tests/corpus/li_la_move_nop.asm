# li_la_move_nop.asm — li, la (label form), move, nop.
.data
msgval: .word 77
.text
main:
    nop
    la   $t0, msgval
    lw   $t1, 0($t0)     # 77
    li   $t2, 5
    move $t3, $t2        # 5
    nop
    andi $a0, $t1, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t3, 0x7f
    li   $v0, 11
    syscall
    li   $v0, 10
    syscall
