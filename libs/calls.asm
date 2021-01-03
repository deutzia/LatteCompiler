bits 64
default rel

global _stradd
global _strcmp
global _strncmp
global printInt
global printString
global readInt
global readString

extern __stradd
extern __stardd
extern __strcmp
extern __strncmp
extern _printInt
extern _printString
extern _readInt
extern _readString

_stradd:
    mov r12, rsp
    lea rdx, [rsp - 8]
    mov rdi, [rdx]
    lea rdx, [rsp - 16]
    mov rsi, [rdx]
    and rsp, 0xFFFFFFFFFFFF0000
    call __stradd
    mov rsp, r12
    mov [rsp], rax
    ret

_strcmp:
    mov r12, rsp
    lea rdx, [rsp - 8]
    mov rdi, [rdx]
    lea rdx, [rsp - 16]
    mov rsi, [rdx]
    and rsp, 0xFFFFFFFFFFFF0000
    call __strcmp
    mov rsp, r12
    mov [rsp], rax
    ret

_strncmp:
    mov r12, rsp
    lea rdx, [rsp - 8]
    mov rdi, [rdx]
    lea rdx, [rsp - 16]
    mov rsi, [rdx]
    and rsp, 0xFFFFFFFFFFFF0000
    call __strncmp
    mov rsp, r12
    mov [rsp], rax
    ret

printInt:
    mov r12, rsp
    lea rdx, [rsp - 8]
    mov rdi, [rdx]
    and rsp, 0xFFFFFFFFFFFF0000
    call _printInt
    mov rsp, r12
    ret

printString:
    mov r12, rsp
    lea rdx, [rsp - 8]
    mov rdi, [rdx]
    and rsp, 0xFFFFFFFFFFFF0000
    call _printString
    mov rsp, r12
    ret

readInt:
    mov r12, rsp
    and rsp, 0xFFFFFFFFFFFF0000
    call _readInt
    mov rsp, r12
    mov [rsp], rax
    ret

readString:
    mov r12, rsp
    and rsp, 0xFFFFFFFFFFFF0000
    call _readString
    mov rsp, r12
    mov [rsp], rax
    ret

