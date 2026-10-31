# syscall_io.asm — exercises syscalls 4 (print string), 1 (print int),
# 11 (print char), 10 (exit) together.
#
# Per docs/spec/INSTRUCTION-REF.md, syscall 1 (PrintInt) writes only
# `Integer.toString` with NO trailing newline added by the syscall itself
# (confirmed empirically against real MARS). Expected combined output:
# "Hi\n" (syscall 4) ++ "42" (syscall 1, no added newline) ++ "!" (syscall 11).
.data
msg: .asciiz "Hi\n"
.text
main:
    li   $v0, 4
    la   $a0, msg
    syscall
    li   $v0, 1
    li   $a0, 42
    syscall
    li   $v0, 11
    li   $a0, 33
    syscall
    li   $v0, 10
    syscall
