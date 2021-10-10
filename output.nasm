section .text
extern print
extern typeError
global our_code_starts_here
our_code_starts_here:
  push RBP
  mov RBP, RSP
  sub RSP, 0x28
  mov RAX, 0xb1a2bc2ec500000
  mov [RBP - 8], RAX
  mov RAX, 0x4
  mov [RBP - 16], RAX
  mov RAX, [RBP - 8]
  push RDI
  mov RDI, RAX
  call print
  pop RDI
  mov [RBP - 24], RAX
  and RAX, 0x1
  cmp RAX, 0
  mov RAX, [RBP - 24]
  jne error_not_number
  mov [RBP - 24], RAX
  mov RAX, [RBP - 16]
  mov [RBP - 32], RAX
  and RAX, 0x1
  cmp RAX, 0
  mov RAX, [RBP - 32]
  jne error_not_number
  mov [RBP - 32], RAX
  cmp [RBP - 24], 0
  jge no_negativo_0_5
  mov [RBP - 24], 0xffffffffffffffff
  imul [RBP - 24], 0xffffffffffffffff
  jmp done_0_5
no_negativo_0_5:
  mov [RBP - 24], 0x1
done_0_5:
  cmp [RBP - 32], 0
  jge no_negativo_2_0_5
  mov [RBP - 16], 0xffffffffffffffff
  imul [RBP - 32], 0xffffffffffffffff
  jmp done_2_0_5
no_negativo_2_0_5:
  mov [RBP - 16], 0x1
done_2_0_5:
  mov RAX, [RBP - 24]
  xor RDX, RDX
  idiv qword[RBP - 32]
  imul RAX, [RBP - 24]
  imul RAX, [RBP - 16]
  mov RSP, RBP
  pop RBP
  ret
error_not_number:
  push RSI
  push RDI
  mov RSI, RAX
  mov RDI, 0x1
  call typeError
error_not_boolean:
  push RSI
  push RDI
  mov RSI, RAX
  mov RDI, 0x2
  call typeError
