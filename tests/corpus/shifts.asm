# shifts.asm — sll, srl, sra.
.text
main:
    li   $t0, 1
    sll  $t1, $t0, 5       # 32
    li   $t2, 0x80000000
    srl  $t3, $t2, 31      # 1
    sra  $t4, $t2, 31      # 0xffffffff
    andi $a0, $t1, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t3, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t4, 0x7f
    li   $v0, 11
    syscall
    li   $v0, 10
    syscall
