# r_arith.asm — add, sub, mult/mflo/mfhi, div/mfhi/mflo.
# No overflow: all operands well within signed 32-bit range.
.text
main:
    li   $t0, 50
    li   $t1, 20
    add  $t2, $t0, $t1       # 70
    sub  $t3, $t0, $t1       # 30
    mult $t0, $t1            # 50*20 = 1000 -> lo=1000, hi=0
    mflo $t4                 # 1000
    div  $t0, $t1            # 50/20 -> lo=2, hi=10
    mfhi $t5                 # 10
    mflo $t6                 # 2
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
