# mem_word.asm — lw/sw including a negative offset.
.data
buf: .word 0, 0, 0, 0
.text
main:
    la   $t0, buf
    addi $t0, $t0, 8      # point at buf+8 (3rd word)
    li   $t1, 123
    sw   $t1, 0($t0)      # store at buf+8
    sw   $t1, -4($t0)     # store same value at buf+4 via negative offset
    lw   $t2, 0($t0)
    lw   $t3, -4($t0)
    andi $a0, $t2, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t3, 0x7f
    li   $v0, 11
    syscall
    li   $v0, 10
    syscall
