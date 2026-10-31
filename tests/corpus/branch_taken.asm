# branch_taken.asm — beq/bne/blez/bgtz, all four conditions TRUE (taken).
# Pattern: seed the "taken" marker (1), then the branch target skips an
# "overwrite to 0" instruction iff the branch is actually taken.
.text
main:
    li   $t0, 5
    li   $t1, 5
    li   $t2, 1
    beq  $t0, $t1, Lbeq
    li   $t2, 0
Lbeq:
    li   $t3, 3
    li   $t4, 4
    li   $t5, 1
    bne  $t3, $t4, Lbne
    li   $t5, 0
Lbne:
    li   $t6, -1
    li   $t7, 1
    blez $t6, Lblez
    li   $t7, 0
Lblez:
    li   $t8, 5
    li   $t9, 1
    bgtz $t8, Lbgtz
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
