open Ast
open Asm

(* Environment *)
type env = (string * int64) list
let empty_env : env = []
let extend_env : string -> int64 -> env -> env =
  fun x v env -> (x, v) :: env

let rec env_lookup (var : string) (env : env) : int64 =
  match env with
  | [] -> failwith "Unbound identifier."
  | (n, slot) :: rest -> if n = var then slot else (env_lookup var rest)

let bool_to_int (b : bool) : int64 =
  if b then 0xA000000000000001 else 0xA000000000000000


let binop_to_instr (op : prim2) (slot : int64) : instruction =
  let params = (Reg RAX, StackPtr (RSP slot)) in
  match op with 
  | Add -> IAdd params
  | And -> IAnd params


let rec compile_expr (e : expr) (env : env) (slot : int64) : instruction list =
  match e with 
  | Id s -> [IMov (Reg RAX, env_lookup s env)]
  | Num n -> [ IMov (Reg RAX, Const n) ] 
  | Bool b -> [IMov (Reg RAX, Const (bool_to_int b))]
  | Prim1 (op, n) -> begin match op with
                        | Add1 -> [compile_expr n env slot] @ [IAdd (Reg RAX, Const 1)]
                        | Sub1 -> [compile_expr n env slot] @ [ISub (Reg RAX, Const 1)]
                  end
  | Let (x, v, e) -> let new_env : env = extend_env x slot in
                  [compile_expr v env slot]
                @ [IMov (StackPtr (RSP, slot), Reg RAX)]
                @ [compile_expr e new_env (slot + 1)]
  | Prim2 (op, n1, n2) -> [compile_expr n1 env slot] @ [IMov (StackPtr (RSP, slot), Reg RAX)]
                    @ [compile_expr n2 env (slot + 1)] @ [IMov (StackPtr (RSP, (slot + 1)), Reg RAX)]
                    @ [IMov (Reg RAX, StackPtr (RSP, slot))]
                    @ (begin match op with 
                             | Lte -> [ICmp (Reg RAX, StackPtr (RSP, (slot + 1)))]
                                    @ [IJle (IfTrue, IfFalse)] 
                             | _ -> [(binop_to_instr op (slot + 1))]
                      end)
                          
  | _ -> failwith "TO BE DONE!"

let compile e : string =
  let instrs = compile_expr e in
  let prelude ="
section .text
global our_code_starts_here
our_code_starts_here:" in
  prelude ^ pp_instrs (instrs @ [ IRet ])
