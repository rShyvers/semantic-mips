# mod_pow2_base.asm — $t9 = $a0 % 4, signed. MIPS `div`'s remainder takes
# the sign of the dividend (INSTRUCTION-REF "div"), e.g. -1 % 4 = -1, not 3.
.text
main:
    li   $t0, 4
    div  $a0, $t0
    mfhi $t9
    li   $v0, 10
    syscall
