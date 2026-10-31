# jump_jal.asm — j and jal with a "return" (hardcoded j back to the known
# call-site address, since jr is out of v1 scope).
.text
main:
    jal  Lsub
AfterCall:
    move $a0, $t0
    li   $v0, 11
    syscall
    andi $a0, $ra, 0xff
    li   $v0, 11
    syscall
    li   $v0, 10
    syscall
Lsub:
    li   $t0, 65
    j    AfterCall
