# sub_base.asm — $t9 = $a0 - $a1, direct subtraction. Uses `subu` (not
# `sub`) so the result is plain 32-bit wraparound subtraction with no
# overflow trap — the property the bitwise variant (sub_twos_complement.asm)
# is claimed to match exactly, for every input, with no overflow edge case
# to reconcile.
.text
main:
    subu $t9, $a0, $a1
    li   $v0, 10
    syscall
