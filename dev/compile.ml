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

let rsp_pointer (slot : int64) : arg = StackPtr (RSP, slot)
let rax = Reg RAX


let const_factory (n : int64) : arg = Const n

let iMov_arg_arg (arg1 : arg) (arg2 : arg) : instruction = IMov (arg1, arg2)
let iMov_arg_const (arg1 : arg) (n : int64) : instruction = IMov (arg1, const_factory n)
let iMov_arg_to_RAX (arg : arg) : instruction = iMov_arg_arg rax arg
let iMov_const_to_RAX (n : int64) : instruction = iMov_arg_const rax n

let iAdd_arg_arg (arg1 : arg) (arg2 : arg) : instruction = IAdd (arg1, arg2)
let iAdd_arg_const (arg1 : arg) (n : int64) : instruction = IAdd (arg1, const_factory n)

let iAnd_arg_arg (arg1 : arg) (arg2 : arg) : instruction = IAnd (arg1, arg2)
let iAnd_arg_const (arg1 : arg) (n : int64) : instruction = IAnd (arg1, const_factory n)

let iSub_arg_arg (arg1 : arg) (arg2 : arg) : instruction = ISub (arg1, arg2)
let iSub_arg_const (arg1 : arg) (n : int64) : instruction = ISub (arg1, const_factory n)

let iCmp_arg_arg (arg1 : arg) (arg2 : arg) : instruction = ICmp (arg1, arg2)
let iCmp_arg_const (arg1 : arg) (n : int64) : instruction = ICmp (arg1, const_factory n)

let i_jmp (label : string) : instruction = IJmp label
let i_je (label : string) : instruction = IJe label
let i_jg (label : string) : instruction = IJg label
let i_label (label : string) : instruction = ILabel label


let compile_lte (rax: arg) (rsp_ptr: arg) (tag : int) : instruction list = 
  let else_label = sprintf "if_false_%d" tag in
  let done_label = sprintf "done_%d" tag in
  let iMov_bool_to_rax (b : bool) = iMov_arg_const rax (bool_to_int b) in
  [iCmp_arg_arg rax rsp_ptr;
   i_jg else_label;
   iMov_bool_to_rax true;
   i_jmp done_label;
   i_label else_label;
   iMov_bool_to_rax false; 
   i_label done_label]


let binop_to_instr (op : prim2) (slot : int64) (tag : int) : instruction list =
  let rsp_ptr = rsp_pointer slot in
  let as_list (fn : (arg -> arg -> instruction)) : (arg -> arg -> instruction list) =
    let ret_fn (arg1 : arg) (arg2 : arg) : instruction list = [fn arg1 arg2] in
    ret_fn
  in
  let compile_lte_with_tag (rax : arg) (rsp_ptr : arg) : instruction list =
    compile_lte rax rsp_ptr tag
  in
  let builder =
    match op with
    | Add -> as_list iAdd_arg_arg
    | And -> as_list iAnd_arg_arg
    | Lte -> compile_lte_with_tag
  in
  builder rax rsp_ptr
  (*match op with 
  | Add -> [iAdd_arg_arg rax rsp_ptr]
  | And -> [iAnd_arg_arg rax rsp_ptr]
  | Lte -> compile_lte rax rsp_ptr tag*)

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


let unop_to_instr_list (compiled_n : instruction list) (op: prim1) (rax: arg) : instruction list =
  let builder =
    match op with
    | Add1 -> iAdd_arg_const
    | Sub1 -> iSub_arg_const
  in
  compiled_n @ [builder rax 2L]


let rec compile_expr (e : tag texpr) (slot_env : slot_env) (slot : int64) : instruction list =
  let next_slot = (Int64.add slot 1L) in
  let rsp_ptr = rsp_pointer slot in
  let mov_rax_to_rsp = iMov_arg_arg rsp_ptr rax in
  let compile_prim1 (op: prim1) (n: tag texpr) : instruction list =
    let compiled_n = (compile_expr n slot_env slot) in
    unop_to_instr_list compiled_n op rax
  in
  let compile_prim2 (op : prim2) (n1 : tag texpr) (n2 : tag texpr) (tag : int) : instruction list =
    let compile_e (n : tag texpr) (slot : int64): instruction list = compile_expr n slot_env slot in
    (compile_e n1 slot) @ [mov_rax_to_rsp]
    @ (compile_e n2 next_slot) 
    @ [iMov_arg_arg (rsp_pointer next_slot) rax]
    @ [iMov_arg_arg rax rsp_ptr]
    @ (binop_to_instr op next_slot tag)
  in
  let compile_let (x : string) (v : tag texpr) (e : tag texpr) : instruction list =
    let new_slot_env : slot_env = extend_slot_env x slot slot_env in
      (compile_expr v slot_env slot)
      @ [mov_rax_to_rsp]
      @ (compile_expr e new_slot_env next_slot)
  in
  let compile_if (cond : tag texpr) (thn : tag texpr) (els : tag texpr) (tag : int) : instruction list =
    let else_label = sprintf "if_false_%d" tag in
    let done_label = sprintf "done_%d" tag in
    let compile_e (e : tag texpr) : instruction list = compile_expr e slot_env slot in
    (compile_e cond) @
    [
      iCmp_arg_const rax (bool_to_int false);
      i_je else_label
    ]
    @ (compile_e thn)
    @ [ i_jmp done_label; i_label else_label ]
    @ (compile_e els)
    @ [ i_label done_label ]
  in
  
  match e with 
  | TId (s, _) -> [iMov_arg_to_RAX (rsp_pointer (slot_env_lookup s slot_env))]
  | TNum (n, _) -> [iMov_const_to_RAX (Int64.shift_left n 1)]
  | TBool (b, _) -> [iMov_const_to_RAX (bool_to_int b)]
  | TPrim1 (op, n, _) -> compile_prim1 op n
  | TLet (x, v, e, _) -> compile_let x v e
  | TPrim2 (op, n1, n2, tag) -> compile_prim2 op n1 n2 tag
  | TIf(cond, thn, els, tag) -> compile_if cond thn els tag
                          
  (*| _ -> failwith "TO BE DONE!"*)

let compile e : string =
  let tagged = tag e in
  let instrs = compile_expr tagged empty_slot_env 1L in
  let prelude ="
section .text
global our_code_starts_here
our_code_starts_here:" in
  prelude ^ pp_instrs (instrs @ [ IRet ])
