# sub_twos_complement.asm — $t9 = $a0 - $a1, computed with no subtract
# instruction at all: negate $a1 bitwise (two's complement: ~y + 1, where
# `nor $t,$a1,$zero` computes ~$a1) and add. x - y = x + (~y + 1) mod 2^32
# always, for every pair of 32-bit values, so this is claimed equivalent to
# sub_base.asm's `subu` unconditionally — no bias correction, no excluded
# input, unlike the div/mod pairs above.
.text
main:
    nor   $t0, $a1, $zero    # t0 = ~$a1
    addiu $t1, $t0, 1        # t1 = ~$a1 + 1 = -$a1 (mod 2^32)
    addu  $t9, $a0, $t1      # t9 = $a0 + (-$a1) = $a0 - $a1 (mod 2^32)
    li    $v0, 10
    syscall
