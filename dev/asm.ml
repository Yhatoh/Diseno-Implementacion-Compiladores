open Printf

(* registers *)
type reg = 
| RAX
| RSP
| RBP
| RDI
| RSI
| RDX
| RCX
| R8
| R9
| R15
| R10
| R11


(* arguments for instructions *)
type arg =
| Const of int64
| Reg of reg
| Ptr of reg * int64
| FLabel of string

let rax = Reg RAX
let rsp = Reg RSP
let rbp = Reg RBP
let rdi = Reg RDI
let rsi = Reg RSI
let rdx = Reg RDX
let rcx = Reg RCX
let r8 = Reg R8
let r9 = Reg R9
let r10 = Reg R10
let r11 = Reg R11
let r15 = Reg R15


(* asm instructions *)
type instruction =
| IRet
| IMov of arg * arg
| IAdd of arg * arg
| ISub of arg * arg
| IMul of arg * arg
| IDiv of arg * arg
| IAnd of arg * arg
| IOr of arg * arg
| IXor of arg * arg
| IShr of arg * arg
| IShl of arg * arg
| ISar of arg * arg
| ISal of arg * arg
| INot of arg
| ICmp of arg * arg
| IJmp of string
| IJe of string
| IJne of string
| IJle of string
| IJl of string
| IJg of string
| IJge of string
| ILabel of string
| IPush of arg
| IPop of arg
| ICall of string
| ICqo
(* TO BE COMPLETED *)

(* Factory functions of above instructions. *)
let const_factory (n : int64) : arg = Const n

let iMov_arg_arg (arg1 : arg) (arg2 : arg) : instruction = IMov (arg1, arg2)
let iMov_arg_const (arg1 : arg) (n : int64) : instruction = IMov (arg1, const_factory n)
let iMov_arg_to_RAX (arg : arg) : instruction = iMov_arg_arg rax arg
let iMov_const_to_RAX (n : int64) : instruction = iMov_arg_const rax n

let iAdd_arg_arg (arg1 : arg) (arg2 : arg) : instruction = IAdd (arg1, arg2)
let iAdd_arg_const (arg1 : arg) (n : int64) : instruction = IAdd (arg1, const_factory n)

let iAnd_arg_arg (arg1 : arg) (arg2 : arg) : instruction = IAnd (arg1, arg2)
let iAnd_arg_const (arg1 : arg) (n : int64) : instruction = IAnd (arg1, const_factory n)

let iXor_arg_arg (arg1 : arg) (arg2 : arg) : instruction = IXor (arg1, arg2)
let iXor_arg_const (arg1 : arg) (n : int64) : instruction = IXor (arg1, const_factory n)

let iSub_arg_arg (arg1 : arg) (arg2 : arg) : instruction = ISub (arg1, arg2)
let iSub_arg_const (arg1 : arg) (n : int64) : instruction = ISub (arg1, const_factory n)

let iMul_arg_arg (arg1 : arg) (arg2 : arg) : instruction = IMul (arg1, arg2)
let iMul_arg_const (arg1 : arg) (n : int64) : instruction = IMul (arg1, const_factory n)

let iDiv_arg_arg (arg1 : arg) (arg2 : arg) : instruction = IDiv (arg1, arg2)
let iDiv_arg_const (arg1 : arg) (n : int64) : instruction = IDiv (arg1, const_factory n)

let iCmp_arg_arg (arg1 : arg) (arg2 : arg) : instruction = ICmp (arg1, arg2)
let iCmp_arg_const (arg1 : arg) (n : int64) : instruction = ICmp (arg1, const_factory n)

let iSar (a : arg) (sh_n : int64) : instruction = ISar (a, (Const sh_n))
let iSal (a : arg) (sh_n : int64) : instruction = ISal (a, (Const sh_n))

let iNot_arg (a : arg) : instruction = INot a

let i_jmp (label : string) : instruction = IJmp label
let i_je (label : string) : instruction = IJe label
let i_jne (label : string) : instruction = IJne label
let i_jg (label : string) : instruction = IJg label
let i_label (label : string) : instruction = ILabel label

let iPush (a : arg) : instruction = IPush a
let iPop (a : arg) : instruction = IPop a

let iCall (f_str : string) : instruction = ICall f_str
let iCall_print : instruction = iCall "print"
let iCall_error_not_number = iCall "error_not_number"
let iCall_error_not_boolean = iCall "error_not_boolean"



let pp_int (num : int64) : string =
  if num > 0L then (sprintf " + %Ld" num) 
  else (if num < 0L then (sprintf " - %Ld" (Int64.mul Int64.minus_one num))
        else "")

let pp_reg reg : string =
  match reg with
  | RAX -> "RAX"
  | RBP -> "RBP"
  | RSP -> "RSP"
  | RDI -> "RDI"
  | RSI -> "RSI"
  | RDX -> "RDX" 
  | RCX -> "RCX"
  | R8 -> "R8"
  | R9 -> "R9"
  | R10 -> "R10"
  | R11 -> "R11"
  | R15 -> "R15"

let pp_arg arg : string =
  match arg with
  | Const n -> sprintf "%#Lx" n
  | Reg r -> pp_reg r
  | Ptr (r, n) -> sprintf "qword[%s%s]" (pp_reg r) (pp_int (Int64.mul 8L n))
  | FLabel s -> s

let pp_instr instr : string =
  match instr with
  | IRet -> "  ret" 
  | IMov (a1, a2) -> sprintf "  mov %s, %s" (pp_arg a1) (pp_arg a2)
  | IAdd (a1, a2) -> sprintf "  add %s, %s" (pp_arg a1) (pp_arg a2)
  | ISub (a1, a2) -> sprintf "  sub %s, %s" (pp_arg a1) (pp_arg a2)
  | IMul (a1, a2) -> sprintf "  imul %s, %s" (pp_arg a1) (pp_arg a2)
  | IDiv (_, a2) -> sprintf "  idiv %s" (pp_arg a2) (* TODO: erase CQO instruction from here *)
  | IAnd (a1, a2) -> sprintf "  and %s, %s" (pp_arg a1) (pp_arg a2)
  | IXor (a1, a2) -> sprintf "  xor %s, %s" (pp_arg a1) (pp_arg a2)
  | IOr (a1, a2) -> sprintf "  or %s, %s" (pp_arg a1) (pp_arg a2)
  | IShr (a1, a2) -> sprintf "  shr %s, %s" (pp_arg a1) (pp_arg a2)
  | IShl (a1, a2) -> sprintf "  shl %s, %s" (pp_arg a1) (pp_arg a2)
  | ISar (a1, a2) -> sprintf "  sar %s, %s" (pp_arg a1) (pp_arg a2)
  | ISal (a1, a2) -> sprintf "  sal %s, %s" (pp_arg a1) (pp_arg a2)
  | INot a -> sprintf "  not %s" (pp_arg a)
  | ICmp (a1, a2) -> sprintf "  cmp %s, %s" (pp_arg a1) (pp_arg a2)
  | IJmp tg -> sprintf "  jmp %s" tg
  | IJe tg -> sprintf "  je %s" tg
  | IJne tg -> sprintf "  jne %s" tg
  | IJle tg -> sprintf "  jle %s" tg
  | IJl tg -> sprintf "  jl %s" tg
  | IJg tg -> sprintf "  jg %s" tg
  | IJge tg -> sprintf "  jge %s" tg
  | ILabel tg -> sprintf "%s:" tg
  | IPush a -> sprintf "  push %s" (pp_arg a)
  | IPop a -> sprintf "  pop %s" (pp_arg a)
  | ICall s -> sprintf "  call %s" s
  | ICqo -> "  cqo"
  (* TO BE COMPLETED *)

let pp_instrs (instrs : instruction list) : string =
  List.fold_left (fun res i -> res ^ "\n" ^ (pp_instr i)) "" instrs
