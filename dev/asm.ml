open Printf

(* registers *)
type reg = 
| RAX
| RSP

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
| StackPtr of reg * int64

(* asm instructions *)
type instruction =
| IRet
| IMov of arg * arg
| IAdd of arg * arg
| ISub of arg * arg
| IAnd of arg * arg
| INot of arg
| ICmp of arg * arg
| IJmp of string
| IJe of string
| IJle of string
| IJg of string
| ILabel of string
(* TO BE COMPLETED *)

let pp_reg reg : string =
  match reg with
  | RAX -> "RAX"
  | RSP -> "RSP"

let pp_arg arg : string =
  match arg with
  | Const n -> sprintf "%#Lx" n
  | Reg r -> pp_reg r
  | StackPtr (r, n) -> sprintf "[%s - %Ld]" (pp_reg r) (Int64.mul 8L n)

let pp_instr instr : string =
  match instr with
  | IRet -> "  ret" 
  | IMov (a1, a2) -> sprintf "  mov %s, %s" (pp_arg a1) (pp_arg a2)
  | IAdd (a1, a2) -> sprintf "  add %s, %s" (pp_arg a1) (pp_arg a2)
  | ISub (a1, a2) -> sprintf "  sub %s, %s" (pp_arg a1) (pp_arg a2)
  | IAnd (a1, a2) -> sprintf "  and %s, %s" (pp_arg a1) (pp_arg a2)
  | INot a -> sprintf "  not %s" (pp_arg a)
  | ICmp (a1, a2) -> sprintf "  cmp %s, %s" (pp_arg a1) (pp_arg a2)
  | IJmp tg -> sprintf "  jmp %s" tg
  | IJe tg -> sprintf "  je %s" tg
  | IJle tg -> sprintf "  jle %s" tg
  | IJg tg -> sprintf "  jg %s" tg
  | ILabel tg -> sprintf "%s:" tg
  (* TO BE COMPLETED *)

let pp_instrs (instrs : instruction list) : string =
  List.fold_left (fun res i -> res ^ "\n" ^ (pp_instr i)) "" instrs
