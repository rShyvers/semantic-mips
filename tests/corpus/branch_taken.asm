# branch_taken.asm — beq/bne/blez/bgtz, all four conditions TRUE (taken).
# Pattern: seed the "taken" marker (1), then the branch target skips an
# "overwrite to 0" instruction iff the branch is actually taken.
#
# Real MIPS32 branches always execute the instruction in their delay slot
# (the one immediately following the branch) before transferring control —
# see docs/spec/SPEC-NOTES.md §9 item 1. Each branch below is therefore
# followed by a genuine no-op (`sll $zero, $zero, 0`, i.e. $zero <<= 0, into
# $zero) as its delay-slot instruction, so the "overwrite to 0" instruction
# stays the first instruction *after* the delay slot, exactly as this
# file's test intent requires under both our delay-slot-aware engine (which
# executes the nop harmlessly) and real MARS's still-no-delay-slot default
# config (which skips it harmlessly).
.text
main:
    li   $t0, 5
    li   $t1, 5
    li   $t2, 1
    beq  $t0, $t1, Lbeq
    sll  $zero, $zero, 0
    li   $t2, 0
Lbeq:
    li   $t3, 3
    li   $t4, 4
    li   $t5, 1
    bne  $t3, $t4, Lbne
    sll  $zero, $zero, 0
    li   $t5, 0
Lbne:
    li   $t6, -1
    li   $t7, 1
    blez $t6, Lblez
    sll  $zero, $zero, 0
    li   $t7, 0
Lblez:
    li   $t8, 5
    li   $t9, 1
    bgtz $t8, Lbgtz
    sll  $zero, $zero, 0
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
