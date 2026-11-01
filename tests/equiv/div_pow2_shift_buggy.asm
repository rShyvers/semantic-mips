# div_pow2_shift_buggy.asm — the classic WRONG "replace division by a power
# of two with a right shift" optimization. `sra` rounds toward negative
# infinity, but MIPS signed `div` (div_pow2_base.asm) rounds toward zero;
# the two disagree on every negative dividend that isn't an exact multiple
# of 4 (e.g. -1 / 4: div gives 0, this gives -1). EquivHarness is expected
# to report this pair as NOT equivalent — it exists to prove the harness
# actually catches a real, classic bug, not just confirm correct code.
.text
main:
    sra  $t9, $a0, 2
    li   $v0, 10
    syscall
