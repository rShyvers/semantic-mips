# mul_pow2_shift.asm — $t9 = $a0 * 8, computed as a left shift instead of a
# multiply. Claimed equivalent to mul_pow2_base.asm for every 32-bit input:
# left-shift by k and multiply-by-2^k agree exactly modulo 2^32, and neither
# `sll` nor `mult`/`mflo` traps on overflow (unlike `add`/`sub`), so there is
# no edge case where the two diverge.
.text
main:
    sll  $t9, $a0, 3
    li   $v0, 10
    syscall
