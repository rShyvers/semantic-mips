# mul_pow2_base.asm — $t9 = $a0 * 8, computed with the direct arithmetic
# instruction (mult/mflo). Input: $a0 (signed). Output: $t9. Exits cleanly
# (syscall 10) so EquivHarness can read $t9 back.
.text
main:
    li   $t0, 8
    mult $a0, $t0
    mflo $t9
    li   $v0, 10
    syscall
