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

(* tags *)
(*
type tag =
| Tag of string
| IfTrue of int64
| IfFalse of int64
| IfDone of int64
*)

(* arguments for instructions *)
type arg =
| Const of int64
| Reg of reg
| Ptr of reg * int64

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
(* TO BE COMPLETED *)

let pp_int (num : int64) : string =
  if num >= 0L then (sprintf "+ %Ld" num) else (sprintf "- %Ld" (Int64.mul Int64.minus_one num))

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

let pp_arg arg : string =
  match arg with
  | Const n -> sprintf "%#Lx" n
  | Reg r -> pp_reg r
  | Ptr (r, n) -> sprintf "[%s %s]" (pp_reg r) (pp_int (Int64.mul 8L n))

let pp_instr instr : string =
  match instr with
  | IRet -> "  ret" 
  | IMov (a1, a2) -> sprintf "  mov %s, %s" (pp_arg a1) (pp_arg a2)
  | IAdd (a1, a2) -> sprintf "  add %s, %s" (pp_arg a1) (pp_arg a2)
  | ISub (a1, a2) -> sprintf "  sub %s, %s" (pp_arg a1) (pp_arg a2)
  | IMul (a1, a2) -> sprintf "  imul %s, %s" (pp_arg a1) (pp_arg a2)
  | IDiv (_, a2) -> sprintf "  CQO\n  idiv qword%s" (pp_arg a2)
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
  (* TO BE COMPLETED *)

let pp_instrs (instrs : instruction list) : string =
  List.fold_left (fun res i -> res ^ "\n" ^ (pp_instr i)) "" instrs
