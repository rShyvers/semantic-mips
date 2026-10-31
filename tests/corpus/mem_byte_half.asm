# mem_byte_half.asm — lb/lbu/lh/lhu/sh.
#
# NOTE: kept deliberately endian-invariant (see docs/spec/SPEC-NOTES.md §9 —
# MARS 4.5 headless defaults to little-endian storage, while our language
# spec is big-endian per the ISA): `lb`/`lbu` read individually-addressed
# `.byte` cells (no multi-byte composition, so byte order can't matter), and
# `lh`/`lhu` round-trip through an `sh` at the *same* address (write-then-read
# within one engine's own convention always agrees, regardless of which
# convention that is).
#
# `bytebuf` is padded to exactly 4 bytes so `halfbuf`'s label sits on an
# already-word-aligned boundary — see DiffHarness report: `Asm.lean`'s
# `layoutLine` records a label's address *before* applying the alignment
# padding required by the directive that follows it on the same line, so a
# label on a `.word`/`.half` directive immediately after a non-multiple-of-4
# `.byte` run resolves to the wrong (pre-padding, misaligned) address.
.data
bytebuf: .byte 0x12, 0xff, 0x05, 0x00
halfbuf: .word 0
.text
main:
    la   $t0, bytebuf
    lb   $t1, 0($t0)      # 0x12 sign-extends positive = 18
    lbu  $t2, 1($t0)      # 0xff zero-extends = 255
    lb   $t3, 2($t0)      # 0x05 = 5
    la   $t6, halfbuf
    li   $t7, 0x8003
    sh   $t7, 0($t6)      # store half
    lh   $t4, 0($t6)      # round-trip: 0x8003 sign-extends negative, low byte 3
    lhu  $t5, 0($t6)      # round-trip: 0x8003 zero-extends, low byte 3
    andi $a0, $t1, 0xff
    li   $v0, 11
    syscall
    andi $a0, $t2, 0xff
    li   $v0, 11
    syscall
    andi $a0, $t3, 0xff
    li   $v0, 11
    syscall
    andi $a0, $t4, 0xff
    li   $v0, 11
    syscall
    andi $a0, $t5, 0xff
    li   $v0, 11
    syscall
    li   $v0, 10
    syscall
