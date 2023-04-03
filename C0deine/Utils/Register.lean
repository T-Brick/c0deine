import C0deine.Utils.ValueSize

/-
  Registers and utilities for x86-64 assembly.
 -/

namespace C0deine

inductive Register
| rax
| rbx
| rcx
| rdx
| rsi
| rdi
| rbp
| rsp
| r8
| r9
| r10
| r11
| r12
| r13
| r14
| r15

namespace Register

def num_registers := 16
def return_val    := rax
def stack_pointer := rsp
def base_pointer := rbp
def arg_registers := [rdi, rsi, rdx, rcx, r8, r9]
-- rbp is included but we are using as base pointer
def callee_saved  := [rbx, r12, r13, r14, r15]
-- r11 is also caller saved but we aren't using it so we exclude
def caller_saved  := [rdi, rsi, rdx, rcx, r8, r9, r10, rax]


def assignable := [rdi, rsi, rdx, rcx, r8, r9, r10, rax, rbx, r12, r13, r14, r15]
def swap_reg := r11
def base_reg := r9
def index_reg := r10


def byteRegisterString : Register → String
  | rax => "%al"
  | rbx => "%bl"
  | rcx => "%cl"
  | rdx => "%dl"
  | rsi => "%sil"
  | rdi => "%dil"
  | rbp => "%bpl"
  | rsp => "%spl"
  | r8  => "%r8b"
  | r9  => "%r9b"
  | r10 => "%r10b"
  | r11 => "%r11b"
  | r12 => "%r12b"
  | r13 => "%r13b"
  | r14 => "%r14b"
  | r15 => "%r15b"

def wordRegisterString : Register → String
  | rax => "%ax"
  | rbx => "%bx"
  | rcx => "%cx"
  | rdx => "%dx"
  | rsi => "%si"
  | rdi => "%di"
  | rbp => "%bp"
  | rsp => "%sp"
  | r8  => "%r8w"
  | r9  => "%r9w"
  | r10 => "%r10w"
  | r11 => "%r11w"
  | r12 => "%r12w"
  | r13 => "%r13w"
  | r14 => "%r14w"
  | r15 => "%r15w"

def doubleRegisterString : Register → String
  | rax => "%eax"
  | rbx => "%ebx"
  | rcx => "%ecx"
  | rdx => "%edx"
  | rsi => "%esi"
  | rdi => "%edi"
  | rbp => "%ebp"
  | rsp => "%esp"
  | r8  => "%r8d"
  | r9  => "%r9d"
  | r10 => "%r10d"
  | r11 => "%r11d"
  | r12 => "%r12d"
  | r13 => "%r13d"
  | r14 => "%r14d"
  | r15 => "%r15d"

def quadRegisterString : Register → String
  | rax => "%rax"
  | rbx => "%rbx"
  | rcx => "%rcx"
  | rdx => "%rdx"
  | rsi => "%rsi"
  | rdi => "%rdi"
  | rbp => "%rbp"
  | rsp => "%rsp"
  | r8  => "%r8"
  | r9  => "%r9"
  | r10 => "%r10"
  | r11 => "%r11"
  | r12 => "%r12"
  | r13 => "%r13"
  | r14 => "%r14"
  | r15 => "%r15"

instance : ToString (Register) where toString := quadRegisterString

end Register


def SizedRegister := Sized Register

namespace SizedRegister

def register (sreg : SizedRegister) : Register := sreg.data

def toString (sreg : SizedRegister) : String :=
  match sreg.size with
  | .byte => Register.byteRegisterString sreg.register
  | .word => Register.wordRegisterString sreg.register
  | .double => Register.doubleRegisterString sreg.register
  | .quad => Register.quadRegisterString sreg.register
instance : ToString (SizedRegister) where toString := SizedRegister.toString

end SizedRegister

