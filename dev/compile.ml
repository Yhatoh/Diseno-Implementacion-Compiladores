open Ast
open Asm
open Printf
open Regsandstack

let bool_to_int (b : bool) : int64 =
  if b then 3L else 1L

let rsp_pointer (slot : int64) : arg = Ptr (RSP, slot)
let rbp_pointer (slot : int64) : arg = Ptr (RBP, slot)


(* Type checking of operations*)
let check_rax_is_type_instr (tp : int64) (slot : int64) : instruction list =
  let label = if tp = 0L then "error_not_number" else "error_not_boolean" in
  [
    iMov_arg_arg (rbp_pointer slot) rax;
    iAnd_arg_const rax 1L;
    iCmp_arg_const rax tp;
    iMov_arg_to_RAX (rbp_pointer slot);
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
  | Add | Sub | Mul | Div | Lte -> check_rax_is_int_instr slot
  | And -> check_rax_is_bool_instr slot

(* Protocol for setting stack before and after a function execution *)
let function_start (n_local_vars : int64) : instruction list =
  [
    iPush rbp ;
    iMov_arg_arg rbp rsp ;
    iSub_arg_const rsp (Int64.mul 8L (n_local_vars))
  ]

let function_end : instruction list =
  [
    iMov_arg_arg rsp rbp ;
    iPop rbp;
    IRet
  ]

(* Compile <= *)
let compile_lte (rax: arg) (rbp_ptr: arg) (tag : int) (tag_fun : int): instruction list = 
  let else_label = sprintf "if_false_%d_%d" tag_fun tag in
  let done_label = sprintf "done_%d_%d" tag_fun tag in
  let iMov_bool_to_rax (b : bool) = iMov_arg_const rax (bool_to_int b) in
  [
    iCmp_arg_arg rax rbp_ptr;
    i_jg else_label;
    iMov_bool_to_rax true;
    i_jmp done_label;
    i_label else_label;
    iMov_bool_to_rax false; 
    i_label done_label
  ]

(* Transforms a binary operation to an instruction type structure *)
let binop_to_instr (op : prim2) (slot : int64) (tag : int) (tag_fun : int) : instruction list =
  let rbp_ptr = rbp_pointer slot in
  let as_list (fn : (arg -> arg -> instruction)) : (arg -> arg -> instruction list) =
    let ret_fn (arg1 : arg) (arg2 : arg) : instruction list = [fn arg1 arg2] in
    ret_fn
  in
  let compile_lte_with_tag (rax : arg) (rbp_ptr : arg) : instruction list =
    compile_lte rax rbp_ptr tag tag_fun
  in
  let builder =
    match op with
    | Add -> as_list iAdd_arg_arg
    | Sub -> as_list iSub_arg_arg
    | Mul -> as_list iMul_arg_arg
    | Div -> as_list iDiv_arg_arg
    | And -> as_list iAnd_arg_arg
    | Lte -> compile_lte_with_tag
  in
  builder rax rbp_ptr

(* Transforms a unary operation to a list of instruction type structures *)
let unop_to_instr_list (op: prim1) : instruction list =
  let iAdd1_arg_list (a : arg) : instruction list = [iAdd_arg_const a 2L] in
  let iSub1_arg_list (a : arg) : instruction list = [iSub_arg_const a 2L] in
  let iNot_arg_list (a : arg) : instruction list = [iNot_arg a ; iAdd_arg_const a 1L] in
  let iPrint_arg_list (a : arg) : instruction list = [
    store_arg 1 rax ;
    move_arg_1_to_6 1 a ;
    iCall_print ;
    pop_arg 1
  ] in
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

(* Takes a parsed program and tags all expressions within *)
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
      in
      let (tagged_args, next_tag) = tag_list args cur in
      (TApply(f_name, tagged_args, cur), next_tag)
  in
  let (tagged, _) = help e 1 in tagged;;

(* Tags the content of an inner function *)
let rec tag_funs (flist : fundef list) (n : int) : tag tfun_def list =
  match flist with
  | [] -> []
  | DefFun (name, arg_names, e) :: tail -> TDefFun (name, arg_names, tag_expr e, n) :: tag_funs tail (n + 1)

(* Tags functions and main of the parsed program *)
let tag_prog (prog : prog) : tag tfun_def list * tag texpr = 
  let (funs, main) = prog in
  (tag_funs funs 1, tag_expr main)

(* Counts the number of let-bindings present on a program or function.
   Used to estimate the stack size required for its execution. *)
let rec count_exprs (e : tag texpr) : int64 =
  let add1_i64 (n : int64) : int64 = Int64.add 1L n in
  match e with
  | TLet (_, _, e_let, _) -> add1_i64 (count_exprs e_let)
  | TPrim1 (_, n, _) -> add1_i64 (count_exprs n)
  | TPrim2 (_, e1, e2, _) -> add1_i64 (max (count_exprs e1) (count_exprs e2))
  | TIf (cond, thn, els, _) -> add1_i64 (max (max (count_exprs cond) (count_exprs thn)) (count_exprs els))
  | TApply _ | TId _ | TBool _ | TNum _ -> 1L

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
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | And -> "&&"
    | Lte -> "<=") (string_of_tag_expr e1) (string_of_tag_expr e2)
  | TLet (x, e1, e2, tag) -> sprintf "(tag_%d let (%s %s) %s)" tag x (string_of_tag_expr e1) (string_of_tag_expr e2) 
  | TIf (e1, e2, e3, tag) -> sprintf "(tag_%d if %s %s %s)" tag (string_of_tag_expr e1) (string_of_tag_expr e2) (string_of_tag_expr e3)
  | TApply (nm, args, tag) -> sprintf "(tag_%d %s (%s))" tag nm (String.concat " " (List.map string_of_tag_expr args)) 

(* Transforms a binary bool-bool operation to a list of instruction type structures *)
let binop_boolean_to_instr_list (second_arg_eval : instruction list) (tag : int) (skip_value : bool) : instruction list =
  let skip_label = sprintf "skip_%d" tag in
  [iCmp_arg_const rax (bool_to_int skip_value)]
  @ [i_je skip_label]
  @ second_arg_eval
  @ [i_label skip_label]

(* Compile-inator *)
let rec compile_expr (e : tag texpr) (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) : instruction list =
  let next_slot = (Int64.sub slot 1L) in
  let rbp_ptr = rbp_pointer slot in
  let mov_rax_to_rbp = iMov_arg_arg rbp_ptr rax in

  let compile_tid (s : string) : instruction list =
    let pos_stack = slot_env_lookup s slot_env in 
    let search_var = if (0L >= pos_stack)
                     then rbp_pointer pos_stack
                     else if (pos_stack > 6L)
                     then rbp_pointer (Int64.sub pos_stack 5L)
                     else (Reg (int_to_cc64_reg (Int64.to_int pos_stack))) 
    in
    [iMov_arg_to_RAX (search_var)]
  in
  let compile_prim1 (op: prim1) (n: tag texpr) : instruction list =
    let compiled_n = (compile_expr n slot_env slot fenv tag_fun total_params) in
    let check_over_under_flow (checker_name : string) : instruction list = [
      iMov_arg_arg (rbp_pointer slot) rax;
      iPush rsi; 
      iPush rdi; 
      iMov_arg_arg rdi rax; 
      iMov_arg_const rsi 2L ; 
      iCall checker_name ; 
      iPop rdi ;
      iPop rsi;
      iMov_arg_arg rax (rbp_pointer slot)
    ] in
    (compiled_n) @ (type_of_unops op slot)
    @ (begin match op with
        | Add1 -> check_over_under_flow "check_overflow_add"
        | Sub1 -> check_over_under_flow "check_overflow_sub"
        | _ -> []
      end)
    @ (unop_to_instr_list op)
  in
  let compile_prim2 (op : prim2) (n1 : tag texpr) (n2 : tag texpr) (tag : int) : instruction list =
    let compile_e (n : tag texpr) (slot : int64): instruction list = compile_expr n slot_env slot fenv tag_fun total_params in
    let compiled_e1 = compile_e n1 slot @ type_of_binops op slot in
    let compiled_e2 = compile_e n2 next_slot @ type_of_binops op next_slot in 
    let check_over_under_flow (checker_name : string) : instruction list = [
      iPush rsi; 
      iPush rdi; 
      iMov_arg_arg rdi rbp_ptr; 
      iMov_arg_arg rsi (rbp_pointer next_slot) ; 
      iCall checker_name ; 
      iPop rdi ;
      iPop rsi
    ] in
    let check_zero_division : instruction list = [
      iPush rsi; 
      iPush rdi; 
      iMov_arg_arg rdi (rbp_pointer next_slot) ; 
      iCall ("check_div_by_0") ; 
      iPop rdi;
      iPop rsi
    ] in
    let safe_env_checker : instruction list =
      match op with
      | And | Lte -> []
      | Add -> check_over_under_flow "check_overflow_add"
      | Sub ->check_over_under_flow "check_overflow_sub"
      | Mul -> check_over_under_flow "check_overflow_mul"
      | Div -> check_zero_division
    in
    let second_arg_eval =
      [mov_rax_to_rbp] @
      compiled_e2 @  
      [iMov_arg_arg (rbp_pointer next_slot) rax] @
      safe_env_checker @
      [iMov_arg_arg rax rbp_ptr] @
      binop_to_instr op next_slot tag tag_fun
    in
    compiled_e1
    @ (begin match op with
        | And -> binop_boolean_to_instr_list second_arg_eval tag false
        | Add | Sub | Lte -> second_arg_eval
        | Mul -> second_arg_eval @ [iSar rax 1L]
        | Div -> second_arg_eval @ [iSal rax 1L]
      end)
  in
  let compile_let (x : string) (v : tag texpr) (e : tag texpr) : instruction list =
    let new_slot_env : slot_env = extend_slot_env x slot slot_env in
      (compile_expr v slot_env slot fenv tag_fun total_params)
      @ [mov_rax_to_rbp]
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
  let compile_apply (nm : string) (args : tag texpr list) : instruction list =
    let largs = List.length args in
    let (_, _) = lookup_comp_fenv nm largs fenv in
    let compile_and_push (e : tag texpr) : instruction list =
      compile_expr e slot_env slot fenv tag_fun total_params @ [iPush rax]
    in 
    let compile_and_move (e : tag texpr) (n_param) : instruction list =
      compile_expr e slot_env slot fenv tag_fun total_params @ [(move_arg_1_to_6 n_param rax)]
    in 
    let rec compiles_and_push (args : tag texpr list) (actual_param : int) : instruction list =
      (*let n_param = List.length args in*) 
      match args with
      | [] -> []
      | hd::tl -> 
        (compiles_and_push tl (actual_param + 1)) 
        @ (if actual_param > 6 then (compile_and_push hd) else (compile_and_move hd actual_param))
    in
    let remove_params_7_to_m : instruction list =
      if largs > 6 then [(iAdd_arg_const rsp (Int64.of_int (8 * (largs - 6))))] else []
    in
    (store_first_6_args) 
    @ (compiles_and_push args 1) 
    @ [iCall nm] 
    @ remove_params_7_to_m
    @ pop_first_6_args
  in

  (* Main compile instruction here *)
  match e with 
  | TId (s, _) -> compile_tid s
  | TNum (n, _) -> [iMov_const_to_RAX (Int64.mul n 2L)]
  | TBool (b, _) -> [iMov_const_to_RAX (bool_to_int b)]
  | TPrim1 (op, n, _) -> compile_prim1 op n
  | TLet (x, v, e, _) -> compile_let x v e
  | TPrim2 (op, n1, n2, tag) -> compile_prim2 op n1 n2 tag
  | TIf(cond, thn, els, tag) -> compile_if cond thn els tag
  | TApply(nm, args, _) -> compile_apply nm args
    
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
    (
      [i_label name] @
      function_start (count_exprs e) @
      (compile_expr e arg_values Int64.minus_one compd_fenv tag (List.length arg_values)) @
      function_end @
      instrs,
      compd_fenv
    )

let compile_prog p : string =
  (*let _, e = p in*)
  let (tagged_funcs, tagged_main) = tag_prog p in
  let (intrs_funs, cfenv)  = (compile_funcs tagged_funcs empty_comp_fenv) in 
  let n_lets_main = count_exprs tagged_main in
  let instrs_main = function_start n_lets_main @ compile_expr tagged_main empty_slot_env Int64.minus_one cfenv 0 0 @ function_end in
  let prelude ="
section .text
extern check_overflow_add
extern check_overflow_sub
extern check_overflow_mul
extern check_div_by_0
extern typeError
extern print
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
  prelude ^ pp_instrs (instrs_main)^ pp_instrs intrs_funs ^ error_section
