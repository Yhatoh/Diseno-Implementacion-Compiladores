open Ast
open Asm
open Printf

(* Environment *)
type slot_env = (string * int64) list
let empty_slot_env : slot_env = []
let extend_slot_env : string -> int64 -> slot_env -> slot_env =
  fun x v slot_env -> (x, v) :: slot_env

let rec slot_env_lookup (var : string) (slot_env : slot_env) : int64 =
  match slot_env with
  | [] -> failwith "Unbound identifier."
  | (n, slot) :: rest -> if n = var then slot else (slot_env_lookup var rest)

let bool_to_int (b : bool) : int64 =
  if b then 3L else 1L


let binop_to_instr (op : prim2) (slot : int64) (tag : int) : instruction list =
  match op with 
  | Add -> [IAdd (Reg RAX, StackPtr (RSP, slot))]
  | And -> [IAnd (Reg RAX, StackPtr (RSP, slot))]
  | Lte -> let else_label = sprintf "if_false_%d" tag in
          let done_label = sprintf "done_%d" tag in 
            [ICmp (Reg RAX, StackPtr (RSP, slot));
             IJg (else_label);
             IMov (Reg RAX, Const (bool_to_int true));
             IJmp (done_label);
             ILabel (else_label);
             IMov (Reg RAX, Const (bool_to_int false)); 
             ILabel (done_label)]

(* Algebraic datatype for expressions *)
type 'a texpr = 
  | TNum of int64 * 'a 
  | TBool of bool * 'a
  | TPrim1 of prim1 * 'a texpr * 'a
  | TPrim2 of prim2 * 'a texpr * 'a texpr * 'a
  | TId of string * 'a
  | TLet of string * 'a texpr * 'a texpr * 'a
  | TIf of 'a texpr * 'a texpr * 'a texpr * 'a

type tag = int 

let tag (e : expr) : tag texpr =
  let rec help (e : expr) (cur : tag) : (tag texpr * tag) =
    match e with
    | Prim1(op, e) ->
      let (tag_e, next_tag) = help e (cur + 1) in
      (TPrim1(op, tag_e, cur), next_tag)
    | Prim2(op, e1, e2) ->
      let (tag_e1, next_tag1) = help e1 (cur + 1) in
      let (tag_e2, next_tag2) = help e2 (next_tag1) in
      (TPrim2(op, tag_e1, tag_e2, cur), next_tag2)
    | If(e1, e2, e3) ->
      let (tag_e1, next_tag1) = help e1 (cur + 1) in
      let (tag_e2, next_tag2) = help e2 (next_tag1) in
      let (tag_e3, next_tag3) = help e3 (next_tag2) in
      (TIf(tag_e1, tag_e2, tag_e3, cur), next_tag3)
    | Let(name, e1, e2) ->
      let (tag_e1, next_tag1) = help e1 (cur + 1) in
      let (tag_e2, next_tag2) = help e2 (next_tag1) in
      (TLet(name, tag_e1, tag_e2, cur), next_tag2)
    | Num(num) -> (TNum(num, cur), cur + 1)
    | Bool(b) -> (TBool(b, cur), cur + 1)
    | Id(name) -> (TId(name, cur), cur + 1)
  in
  let (tagged, _) = help e 1 in tagged;;

let rec compile_expr (e : tag texpr) (slot_env : slot_env) (slot : int64) : instruction list =
  match e with 
  | TId (s, _) -> [IMov (Reg RAX, (StackPtr (RSP, (slot_env_lookup s slot_env))))]
  | TNum (n, _) -> [ IMov (Reg RAX, Const (Int64.shift_left n 1)) ] 
  | TBool (b, _) -> [IMov (Reg RAX, Const (bool_to_int b))]
  | TPrim1 (op, n, _) -> begin match op with
                        | Add1 -> (compile_expr n slot_env slot) @ [IAdd (Reg RAX, Const 2L)]
                        | Sub1 -> (compile_expr n slot_env slot) @ [ISub (Reg RAX, Const 2L)]
                  end
  | TLet (x, v, e, _) -> let new_slot_env : slot_env = extend_slot_env x slot slot_env in
                  (compile_expr v slot_env slot)
                @ [IMov (StackPtr (RSP, slot), Reg RAX)]
                @ (compile_expr e new_slot_env (Int64.add slot 1L))
  | TPrim2 (op, n1, n2, tag) -> 
                    (compile_expr n1 slot_env slot) @ [IMov (StackPtr (RSP, slot), Reg RAX)]
                    @ (compile_expr n2 slot_env (Int64.add slot 1L)) 
                    @ [IMov (StackPtr (RSP, (Int64.add slot 1L)), Reg RAX)]
                    @ [IMov (Reg RAX, StackPtr (RSP, slot))]
                    @ (binop_to_instr op (Int64.add slot 1L) tag)
  | TIf(cond, thn, els, tag) ->
    let else_label = sprintf "if_false_%d" tag in
    let done_label = sprintf "done_%d" tag in
    (compile_expr cond slot_env slot) @
    [
      ICmp(Reg(RAX), Const (bool_to_int false));
      IJe(else_label)
    ]
    @ (compile_expr thn slot_env slot)
    @ [ IJmp(done_label); ILabel(else_label) ]
    @ (compile_expr els slot_env slot)
    @ [ ILabel(done_label) ]
                          
  (*| _ -> failwith "TO BE DONE!"*)

let compile e : string =
  let tagged = tag e in
  let instrs = compile_expr tagged empty_slot_env 1L in
  let prelude ="
section .text
global our_code_starts_here
our_code_starts_here:" in
  prelude ^ pp_instrs (instrs @ [ IRet ])
