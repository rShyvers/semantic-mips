# mod_pow2_mask_buggy.asm — the classic WRONG "replace mod-power-of-two with
# a bitmask" optimization. `andi` is a logical mask: it always returns a
# small non-negative value. MIPS signed remainder (mod_pow2_base.asm) takes
# the sign of the dividend, so this disagrees on every negative dividend
# that isn't an exact multiple of 4 (e.g. -1 % 4: div gives -1, this gives
# 3). EquivHarness is expected to report this pair as NOT equivalent.
.text
main:
    andi $t9, $a0, 3
    li   $v0, 10
    syscall
