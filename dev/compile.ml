open Ast
open Asm
open Printf
open Regsandstack

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

let iXor_arg_arg (arg1 : arg) (arg2 : arg) : instruction = IXor (arg1, arg2)
let iXor_arg_const (arg1 : arg) (n : int64) : instruction = IXor (arg1, const_factory n)

let iSub_arg_arg (arg1 : arg) (arg2 : arg) : instruction = ISub (arg1, arg2)
let iSub_arg_const (arg1 : arg) (n : int64) : instruction = ISub (arg1, const_factory n)

let iCmp_arg_arg (arg1 : arg) (arg2 : arg) : instruction = ICmp (arg1, arg2)
let iCmp_arg_const (arg1 : arg) (n : int64) : instruction = ICmp (arg1, const_factory n)

let iNot_arg (a : arg) : instruction = INot a

let i_jmp (label : string) : instruction = IJmp label
let i_je (label : string) : instruction = IJe label
let i_jne (label : string) : instruction = IJne label
let i_jg (label : string) : instruction = IJg label
let i_label (label : string) : instruction = ILabel label

let check_rax_is_type_instr (tp : int64) (slot : int64) : instruction list =
  (*[move rax stackptr, and stackptr type, move rax stackptr + 1, move rax stackptr, cmp stackptr + 1 type, jne error]*)
  let label = if tp = 0L then "error_not_number" else "error_not_boolean" in
  [
    iMov_arg_arg (rsp_pointer slot) rax;
    iAnd_arg_const rax 1L;
    (*iMov_arg_arg (rsp_pointer (Int64.add slot 1L)) rax;*)
    iCmp_arg_const rax tp;
    iMov_arg_to_RAX (rsp_pointer slot);
    i_jne label
  ]

let check_rax_is_int_instr (slot : int64) : instruction list = 
  check_rax_is_type_instr 0L slot

let check_rax_is_bool_instr (slot : int64) : instruction list = 
  check_rax_is_type_instr 1L slot
 
let type_of_unops (operation : prim1) (slot : int64) : instruction list =
  match operation with
  | Add1 | Sub1 -> check_rax_is_int_instr slot
  | Not -> check_rax_is_bool_instr slot
  | Print -> []

let type_of_binops (operation : prim2) (slot : int64) : instruction list =
  match operation with
  | Add | Lte -> check_rax_is_int_instr slot
  | And -> check_rax_is_bool_instr slot

let function_start (total_params : int64) : instruction list =
  [
    IPush (Reg RBP) ;
    iMov_arg_arg (Reg RBP) (Reg RSP) ;
    iSub_arg_const (Reg RSP) (Const (Int64.mul 8L total_params))
  ]

let function_end : instruction list =
  [
    iMov_arg_arg (Reg RSP) (Reg RBP) ;
    IPop (Reg RSP)
    IRet
  ]

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


let unop_to_instr_list (op: prim1) : instruction list =
  let iAdd1_arg_list (a : arg) : instruction list = [iAdd_arg_const a 2L] in
  let iSub1_arg_list (a : arg) : instruction list = [iSub_arg_const a 2L] in
  let iNot_arg_list (a : arg) : instruction list = [iNot_arg a ; iAdd_arg_const a 1L] in
  let iPrint_arg_list (a : arg) : instruction list =
    (store_first_6_args) @ [move_arg_1_to_6 1 a ; ICall "print"] @ (pop_first_6_args) in
  let builder =
    match op with
    | Add1 -> iAdd1_arg_list
    | Sub1 -> iSub1_arg_list
    | Not -> iNot_arg_list
    | Print -> iPrint_arg_list
  in
  builder rax

(* Algebraic datatype for tagged expressions *)
type 'a texpr = 
  | TNum of int64 * 'a 
  | TBool of bool * 'a
  | TPrim1 of prim1 * 'a texpr * 'a
  | TPrim2 of prim2 * 'a texpr * 'a texpr * 'a
  | TId of string * 'a
  | TLet of string * 'a texpr * 'a texpr * 'a
  | TIf of 'a texpr * 'a texpr * 'a texpr * 'a
  | TApply of string * 'a texpr list * 'a

type 'a tfun_def =
  | TDefFun of string * string list * 'a texpr * 'a

type tag = int 

let tag_expr (e : expr) : tag texpr =
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
    | Apply(f_name, args) ->
      let rec tag_list (es : expr list) (sub_cur : tag) =
        match es with
        | [] -> ([], sub_cur)
        | hd :: tl ->
          let (tagged_hd, next_tag1) = help hd (sub_cur + 1) in
          let (tagged_tl, next_tag2) = tag_list tl next_tag1 in
          (tagged_hd :: tagged_tl, next_tag2)
      let (tagged_args, next_tag) = tag_list args cur in
      (TApply(f_name, tagged_args, cur), next_tag)
  in
  let (tagged, _) = help e 1 in tagged;;

let rec tag_funs (flist : fundef list) (n : int) : tag tfun_def list =
  match flist with
  | [] -> []
  | DefFun (name, arg_names, e) :: tail -> TDefFun (name, arg_names, tag_expr e, n) :: tag_funs tail (n + 1)

let tag_prog (prog : prog) : tag tfun_def list * tag texpr = 
  let (funs, main) = prog in
  (tag_funs funs 1, tag_expr main)

(* Pretty printing - used by testing framework *)
let rec string_of_tag_expr(e : tag texpr) : string = 
  match e with
  | TNum (n, tag) -> sprintf "tag_%d %s" tag (Int64.to_string n)
  | TBool (b, tag) -> sprintf "tag_%d %s" tag (if b then "true" else "false")
  | TId (s, tag) -> sprintf "tag_%d %s" tag s
  | TPrim1 (op, e, tag) -> sprintf "(tag_%d %s %s)" tag
    (match op with
    | Add1 -> "add1"
    | Sub1 -> "sub1"
    | Not -> "not"
    | Print -> "print") (string_of_tag_expr e)
  | TPrim2 (op, e1, e2, tag) -> sprintf "(tag_%d %s %s %s)" tag 
    (match op with 
    | Add -> "+"
    | And -> "&&"
    | Lte -> "<=") (string_of_tag_expr e1) (string_of_tag_expr e2)
  | TLet (x, e1, e2, tag) -> sprintf "(tag_%d let (%s %s) %s)" tag x (string_of_tag_expr e1) (string_of_tag_expr e2) 
  | TIf (e1, e2, e3, tag) -> sprintf "(tag_%d if %s %s %s)" tag (string_of_tag_expr e1) (string_of_tag_expr e2) (string_of_tag_expr e3)


let binop_boolean_to_instr_list (second_part : instruction list) (tag : int) (skip_value : bool) : instruction list =
  let skip_label = sprintf "skip_%d" tag in
  [iCmp_arg_const rax (bool_to_int skip_value)]
  @ [i_je skip_label]
  @ second_part
  @ [i_label skip_label]

let rec compile_expr (e : tag texpr) (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) : instruction list =
  let next_slot = (Int64.add slot 1L) in
  let rsp_ptr = rsp_pointer slot in
  let mov_rax_to_rsp = iMov_arg_arg rsp_ptr rax in
  let compile_prim1 (op: prim1) (n: tag texpr) : instruction list =
    let compiled_n = (compile_expr n slot_env slot fenv tag_fun total_params) in
    (compiled_n) @ (type_of_unops op slot) @ (unop_to_instr_list op)
  in
  let compile_prim2 (op : prim2) (n1 : tag texpr) (n2 : tag texpr) (tag : int) : instruction list =
    let compile_e (n : tag texpr) (slot : int64): instruction list = compile_expr n slot_env slot fenv tag_fun total_params in
    let compiled_e1 = compile_e n1 slot @ type_of_binops op slot in
    let compiled_e2 = compile_e n2 next_slot @ type_of_binops op next_slot in 
    let second_part = 
      [mov_rax_to_rsp]
      @ compiled_e2  
      @ [iMov_arg_arg (rsp_pointer next_slot) rax]
      @ [iMov_arg_arg rax rsp_ptr]
      @ (binop_to_instr op next_slot tag)
    in
    compiled_e1
    @ (begin match op with
        | And -> binop_boolean_to_instr_list second_part tag false
        | Add -> second_part
        | Lte -> second_part
      end)
  in
  let compile_let (x : string) (v : tag texpr) (e : tag texpr) : instruction list =
    let new_slot_env : slot_env = extend_slot_env x slot slot_env in
      (compile_expr v slot_env slot fenv tag_fun total_params)
      @ [mov_rax_to_rsp]
      @ (compile_expr e new_slot_env next_slot fenv tag_fun total_params)
  in
  let compile_if (cond : tag texpr) (thn : tag texpr) (els : tag texpr) (tag : int) : instruction list =
    let else_label = sprintf "if_false_%d_%d" tag_fun tag in
    let done_label = sprintf "done_%d_%d" tag_fun tag in
    let compile_e (e : tag texpr) : instruction list = compile_expr e slot_env slot fenv tag_fun total_params in
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
  | TApply(nm, args, _) -> 
    let largs = length args in
    let (_, arg_names) = lookup_comp_fenv nm largs in
    (*calling convention*)
    [ICall nm]


                          
  (*| _ -> failwith "TO BE DONE!"*)

let rec compile_funcs (func_list : tag tfun_def list) (cfenv : comp_fenv) : instruction list * comp_fenv =
  match func_list with
  | [] -> ([], cfenv)
  | TDefFun (name, arg_names, e, tag) :: tail ->
    let extended_comp_fenv : comp_fenv = extend_comp_fenv name arg_names cfenv in
    let (instrs, compd_fenv) = compile_funcs tail extended_comp_fenv in
    let rec add_args_to_env (arg_ids : string list) (slot : int64) : slot_env =
      match arg_ids with
      | [] -> empty_slot_env
      | arg :: tl -> extend_slot_env arg slot (add_args_to_env tl (Int64.add slot 1L))
    in
    let arg_values = add_args_to_env arg_names 1L in
    ([i_label name] @ function_start
                    @ (compile_expr e arg_values (Int64.of_int ((length arg_values) + 1)) comp_fenv tag (length arg_values))
                    @ function_end
                    @ instrs, compd_fenv)

let compile_prog p : string =
  (*let _, e = p in*)
  let (tagged_funcs, tagged_main) = tag_prog p in
  let instrs_main = compile_expr tagged_main empty_slot_env 1L 0 0 in
  let prelude ="
section .text
extern print
extern typeError
global our_code_starts_here
our_code_starts_here:" in
  let error_section = "
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
  call typeError" in
  prelude ^ pp_instrs (instrs @ [ IRet ]) ^ error_section
