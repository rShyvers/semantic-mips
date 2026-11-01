# div_pow2_base.asm — $t9 = $a0 / 4, signed, truncating toward zero (MIPS
# `div`'s actual rounding rule — INSTRUCTION-REF "div").
.text
main:
    li   $t0, 4
    div  $a0, $t0
    mflo $t9
    li   $v0, 10
    syscall
