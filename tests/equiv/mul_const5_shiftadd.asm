# mul_const5_shiftadd.asm — $t9 = $a0 * 5, computed as (x << 2) + x = 4x + x.
# Deliberately uses `addu`, not `add`: `mult`/`mflo` never traps, it just
# returns the low 32 bits of the true product, so the only way to match it
# exactly for every input (including ones where x*5 overflows 32 bits
# signed) is a non-trapping add. With `add` instead, this pair would
# spuriously diverge (halt vs. wrap) on large inputs even though the
# strength-reduction itself is correct — `addu` avoids that.
.text
main:
    sll  $t0, $a0, 2
    addu $t9, $t0, $a0
    li   $v0, 10
    syscall
