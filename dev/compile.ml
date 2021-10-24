open Ast
open Asm
open Printf
open Regsandstack

let add_int_tag : int64 = 4L
let mul_div_shift_correction : int64 = 2L
let bool_tag : int64 = 2L
let int_tag : int64 = 0L
let tup_tag : int64 = 1L
let type_mask : int64 = 3L

let true_bit_int_64 : int64 = 4L
let false_bit_int_64 : int64 = 0L

let bool_to_int (b : bool) : int64 =
  (Int64.add bool_tag (if b then true_bit_int_64 else false_bit_int_64))

(*let a_normal_form_binop (binop : prim2)*)

let rsp_pointer (slot : int64) : arg = Ptr (RSP, slot)
let rbp_pointer (slot : int64) : arg = Ptr (RBP, slot)

(* Type checking of operations*)
let check_rax_is_type_instr (tp : int64) (slot : int64) : instruction list =
  let label = if tp = int_tag 
                then "error_not_number" 
                else (if tp = bool_tag 
                      then "error_not_boolean"
                      else "error_not_tuple") 
  in
  [
    iMov_arg_arg (rbp_pointer slot) rax;
    iAnd_arg_const rax type_mask;
    iCmp_arg_const rax tp;
    iMov_arg_to_RAX (rbp_pointer slot);
    i_jne label
  ]

(* NASM code to verify that the value in RAX is an integer in our language *)
let check_rax_is_int_instr (slot : int64) : instruction list = 
  check_rax_is_type_instr int_tag slot

(* NASM code to verify that the value in RAX is a boolean in our language *)  
let check_rax_is_bool_instr (slot : int64) : instruction list = 
  check_rax_is_type_instr bool_tag slot
 
(* NASM code to verify that the value in RAX is a tuple in our language *)
let check_rax_is_tuple_instr (slot : int64) : instruction list =
  check_rax_is_type_instr tup_tag slot

(* Verifies that the value of the operand of a unary
   operation has a valid type. *)
let type_of_unops (operation : prim1) (slot : int64) : instruction list =
  match operation with
  | Add1 | Sub1 -> check_rax_is_int_instr slot
  | Not -> check_rax_is_bool_instr slot
  | Print -> []

(* Verifies that the values of the operands of a binary
   operation have valid types. *)
let type_of_binops (operation : prim2) (slot : int64) : instruction list =
  match operation with
  | Add | Sub | Mul | Div | Lte -> check_rax_is_int_instr slot
  | And -> check_rax_is_bool_instr slot
  | Get -> []

(* Protocol for setting stack before a function call. *)
let function_start (n_local_vars : int64) : instruction list =
  [
    iPush rbp ;
    iMov_arg_arg rbp rsp ;
    iSub_arg_const rsp (Int64.mul 8L (n_local_vars))
  ]

(* Protocol for recovering scope values
   after an internal function call returns. *)
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
  let compile_div (e1 : arg) (e2 : arg) : instruction list =
    [ICqo; iDiv_arg_arg e1 e2]
  in
  let compile_lte_with_tag (e1 : arg) (e2 : arg) : instruction list =
    compile_lte e1 e2 tag tag_fun
  in
  let compile_get (rax : arg) (rbp_ptr : arg) : instruction list =
    let r10_ptr = Ptr(R10, 0L) in
    let check_index_range = [
      iCmp_arg_const r11 0L ;
      IJl "index_too_low" ;
      iCmp_arg_arg r11 r10_ptr ;
      IJge "index_too_high"
    [
      iPush r10 ;
      iPush r11 ;
      iMov_arg_arg r10 rax
      (*iMov_arg_to_RAX r10*)
    ] @(*[iMov_arg_arg rax r10] @*)
    (check_rax_is_tuple_instr (Int64.sub slot 1L)) @
    [
      iSub_arg_const r10 1L ;
      iMov_arg_arg r11 rbp_ptr ;
      iMov_arg_to_RAX rbp_ptr
    ] @(*[iMov_arg_arg rax rbp_ptr] @*)
    (check_rax_is_int_instr slot) @
    [iMov_arg_arg r11 rbp_ptr] @
    check_index_range @
    [
      iSar r11 2L ;
      iAdd_arg_const r11 1L ;
      iSal r11 3L ;
      iAdd_arg_arg r10 r11 ;
      iMov_arg_to_RAX r10_ptr ;
      iPop r11 ;
      iPop r10
    ] 
  in
  let builder =
    match op with
    | Add -> as_list iAdd_arg_arg
    | Sub -> as_list iSub_arg_arg
    | Mul -> as_list iMul_arg_arg
    | Div -> compile_div
    | And -> as_list iAnd_arg_arg
    | Lte -> compile_lte_with_tag
    | Get -> compile_get
  in
  builder rax rbp_ptr

(* Transforms a unary operation to a list of instruction type structures *)
let unop_to_instr_list (op: prim1) : instruction list =
  let iAdd1_arg_list (a : arg) : instruction list = [iAdd_arg_const a 4L] in
  let iSub1_arg_list (a : arg) : instruction list = [iSub_arg_const a 4L] in
  let iNot_arg_list (a : arg) : instruction list = [iNot_arg a ; iAdd_arg_const a 2L] in
  let iPrint_arg_list (a : arg) : instruction list = 
    store_r10_r11 @
    store_first_6_args @
    [
      move_arg_1_to_6 1 a ;
      iCall_print ;
    ] @
    pop_first_6_args @
    pop_r10_r11 
  in
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
  | TSet of 'a texpr * 'a texpr * 'a texpr * 'a
  | TIf of 'a texpr * 'a texpr * 'a texpr * 'a
  | TApply of string * 'a texpr list * 'a
  | TTuple of 'a texpr list * 'a

(* Algebraic data type for tagged functions *)
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
    | Set(t, pos, value) ->
      let (tag_t, next_tag1) = help t (cur + 1) in
      let (tag_pos, next_tag2) = help pos (next_tag1 + 1) in
      let (tag_value, next_tag3) = help value (next_tag2) in
      (TSet(tag_t, tag_pos, tag_value, cur), next_tag3)
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
    | Tuple(attrs) ->
      (* DUPLICATION ALARM *)
      let rec tag_list (es : expr list) (sub_cur : tag) =
        match es with
        | [] -> ([], sub_cur)
        | hd :: tl ->
          let (tagged_hd, next_tag1) = help hd (sub_cur + 1) in
          let (tagged_tl, next_tag2) = tag_list tl next_tag1 in
          (tagged_hd :: tagged_tl, next_tag2)
      in
      let (tagged_attrs, next_tag) = tag_list attrs cur in
      (TTuple(tagged_attrs, cur), next_tag)
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
  | TId _ | TBool _ | TNum _ -> 1L
  | TApply (_, args, _) ->
    let rec count_tuple_exprs (e_list : tag texpr list) : int64 =
      match e_list with
      | [] -> 0L
      | hd::tl -> Int64.add (count_exprs hd) (count_tuple_exprs tl)
    in
    count_tuple_exprs args
  | TTuple (attrs, _) ->
    let rec count_tuple_exprs (e_list : tag texpr list) : int64 =
      match e_list with
      | [] -> 0L
      | hd::tl -> max (count_exprs hd) (count_tuple_exprs tl)
    in
    (add1_i64 (count_tuple_exprs attrs))
  | TSet (t, pos, value, _) ->
    add1_i64 (Int64.add (Int64.add (count_exprs t) (count_exprs pos)) (count_exprs value))

      

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
    | Lte -> "<="
    | Get -> "get") (string_of_tag_expr e1) (string_of_tag_expr e2)
  | TLet (x, e1, e2, tag) -> sprintf "(tag_%d let (%s %s) %s)" tag x (string_of_tag_expr e1) (string_of_tag_expr e2) 
  | TSet (t, e1, e2, tag) -> sprintf "(tag_%d set %s %s %s)" tag (string_of_tag_expr t) (string_of_tag_expr e1) (string_of_tag_expr e2) 
  | TIf (e1, e2, e3, tag) -> sprintf "(tag_%d if %s %s %s)" tag (string_of_tag_expr e1) (string_of_tag_expr e2) (string_of_tag_expr e3)
  | TApply (nm, args, tag) -> sprintf "(tag_%d %s (%s))" tag nm (String.concat " " (List.map string_of_tag_expr args))
  | TTuple (attrs, tag) -> sprintf "(tag_%d %s)" tag (String.concat " " (List.map string_of_tag_expr attrs))

(* Transforms a binary bool-bool operation to a list of instruction type structures *)
let binop_boolean_to_instr_list (second_arg_eval : instruction list) (tag : int) (tag_fun : int) (skip_value : bool) : instruction list =
  let skip_label = sprintf "skip_%d_%d" tag_fun tag in
  [
    iCmp_arg_const rax (bool_to_int skip_value) ;
    i_je skip_label
  ] @
  second_arg_eval @
  [i_label skip_label]

(* Main compile function.
    arguments:
      e: expression to be compiled
      slot_env: identifier reference environment
      slot: the 8-byte stack slot which currently holds the lastly saved reference.
      fenv: the functions environment
      tag_fun:
      total_params:
    returns:
      the abstract syntax of the NASM code. *)
let rec compile_expr (e : tag texpr) (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) : instruction list =
  let next_slot = (Int64.sub slot 1L) in
  let rbp_ptr = rbp_pointer slot in
  let mov_rax_to_rbp = iMov_arg_arg rbp_ptr rax in
  (* Compiles the value binding to an identifier. *)
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
  (* Compiles a unary operation. *)
  let compile_prim1 (op: prim1) (n: tag texpr) : instruction list =
    let compiled_n = (compile_expr n slot_env slot fenv tag_fun total_params) in
    let check_over_under_flow (checker_name : string) : instruction list = 
      store_r10_r11 @
      store_first_6_args @
      [
        iMov_arg_arg rdi rax; 
        iMov_arg_const rsi 2L ; 
        iCall checker_name ; 
        iPop rdi ;
        iPop rsi;
        iMov_arg_arg rax (rbp_pointer slot)
      ] @
      pop_first_6_args @
      pop_r10_r11 
    in
    (compiled_n) @ (type_of_unops op slot)
    @ (begin match op with
        | Add1 -> check_over_under_flow "check_overflow_add"
        | Sub1 -> check_over_under_flow "check_overflow_sub"
        | _ -> []
      end)
    @ (unop_to_instr_list op)
  in
  (* Compiles a binary operation. *)
  let compile_prim2 (op : prim2) (n1 : tag texpr) (n2 : tag texpr) (tag : int) : instruction list =
    let compile_e (n : tag texpr) (slot : int64): instruction list = compile_expr n slot_env slot fenv tag_fun total_params in
    let compiled_e1 = compile_e n1 slot @ type_of_binops op slot in
    let compiled_e2 = compile_e n2 next_slot @ type_of_binops op next_slot in 
    let check_over_under_flow (checker_name : string) : instruction list =   
      store_r10_r11 @
      store_first_6_args @
      [
        iMov_arg_arg rdi rbp_ptr; 
        iMov_arg_arg rsi (rbp_pointer next_slot) ; 
        iCall checker_name ;
      ] @
      pop_first_6_args @
      pop_r10_r11 
    in
    let check_zero_division : instruction list = 
      store_first_6_args @
      store_r10_r11 @
      [
        iMov_arg_arg rdi (rbp_pointer next_slot) ; 
        iCall ("check_div_by_0") ; 
      ] @
      pop_first_6_args @
      pop_r10_r11 
    in
    let safe_env_checker : instruction list =
      match op with
      | And | Lte | Get -> []
      | Add -> check_over_under_flow "check_overflow_add"
      | Sub -> check_over_under_flow "check_overflow_sub"
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
        | And -> binop_boolean_to_instr_list second_arg_eval tag tag_fun false
        | Add | Sub | Lte -> second_arg_eval
        | Mul -> second_arg_eval @ [iSar rax mul_div_shift_correction]
        | Div -> second_arg_eval @ [iSal rax mul_div_shift_correction]
        | Get -> second_arg_eval (* falta check de la tupla *)
      end)
  in
  (* Compiles a let binding. *)
  let compile_let (x : string) (v : tag texpr) (e : tag texpr) : instruction list =
    let new_slot_env : slot_env = extend_slot_env x slot slot_env in
      (compile_expr v slot_env slot fenv tag_fun total_params)
      @ [mov_rax_to_rbp]
      @ (compile_expr e new_slot_env next_slot fenv tag_fun total_params)
  in
  (* Compiles an if statement *)
  let compile_if (cond : tag texpr) (thn : tag texpr) (els : tag texpr) (tag : int) : instruction list =
    let else_label = sprintf "if_false_%d_%d" tag_fun tag in
    let done_label = sprintf "done_%d_%d" tag_fun tag in
    let compile_e (e : tag texpr) : instruction list = compile_expr e slot_env slot fenv tag_fun total_params in
    (compile_e cond) @ (check_rax_is_bool_instr slot) @
    [
      iCmp_arg_const rax (bool_to_int false);
      i_je else_label
    ]
    @ (compile_e thn)
    @ [ i_jmp done_label; i_label else_label ]
    @ (compile_e els)
    @ [ i_label done_label ]
  in
  (* Compiles a function call. *)
  let compile_apply (nm : string) (args : tag texpr list) : instruction list =
    let largs = List.length args in
    let (_, _) = lookup_comp_fenv nm largs fenv in
    (*let compile_and_save (e : tag texpr) (slot : int64) : instruction list =
      compile_expr e slot_env slot fenv tag_fun total_params
    in
    let rec compiles_and_save (args : tag texpr list)(slot : int64) : instruction list =
      match args with
      | [] -> []
      | hd::tl -> 
        (compile_and_save hd slot) @ [iMov_arg_arg (rbp_pointer slot) rax] @ (compiles_and_save tl (Int64.sub slot 1L))
    in*)
    let rec compiles_and_push (args : tag texpr list) (actual_param : int) : instruction list =
      (*let n_param = List.length args in*) 
      match args with
      | [] -> []
      | _::tl -> 
        compiles_and_push tl (actual_param + 1) @
        [iMov_arg_to_RAX (rbp_pointer (Int64.sub slot (Int64.of_int (actual_param - 1))))]
        @ (if actual_param > 6 then [iPush rax] else [(move_arg_1_to_6 actual_param rax)])
    in
    let remove_params_7_to_m : instruction list =
      if largs > 6 then [(iAdd_arg_const rsp (Int64.of_int (8 * (largs - 6))))] else []
    in
    (*compiles_and_save args slot*)
    (store_r10_r11) 
    @ (store_first_6_args) 
    @ (compiles_and_push args 1) 
    @ [iCall nm] 
    @ remove_params_7_to_m
    @ pop_first_6_args
    @ pop_r10_r11
  in

  (* Compilation of tuple creation. *)
  let compile_tuple (attrs : tag texpr list) : instruction list =
    let compile_tuple_help (lst : tag texpr list) : instruction list =
      let rec compile_lexpr (lst : tag texpr list) (param_pos : int) : instruction list =
        match lst with
        | [] -> []
        | hd::tl -> (compile_expr hd slot_env next_slot fenv tag_fun total_params) @
                    [iMov_arg_arg (Ptr (R11, (Int64.of_int param_pos))) rax] @
                    (compile_lexpr tl (param_pos + 1))
      in
      [
        iPush r11 ;
        iMov_arg_arg r11 r15 ;
        iMov_arg_const (Ptr (R11, 0L)) (Int64.of_int (4 * (List.length attrs))) ;
        iAdd_arg_const r15 (Int64.of_int (8 * (List.length attrs + 1)))
      ] @
      (compile_lexpr lst 1) @
      [
        iMov_arg_to_RAX r11 ;
        iAdd_arg_const rax 1L ;
        iPop r11
      ]
    in
    (compile_tuple_help attrs) @
    [
      iAdd_arg_const r15 7L ;
      iPush r11 ;
      iMov_arg_const r11 (Int64.mul Int64.minus_one 8L) ;
      iAnd_arg_arg r15 r11 ; 
      iPop r11
    ]
  in

  (* Compilation of the set tuple value *)
  let compile_set (t : tag texpr) (pos : tag texpr) (value : tag texpr) : instruction list =
    let compiled_t = compile_expr t slot_env slot fenv tag_fun total_params in 
    let compiled_pos = compile_expr pos slot_env next_slot fenv tag_fun total_params in
    let compiled_value = compile_expr value slot_env (Int64.sub next_slot 1L) fenv tag_fun total_params in 
    let check_index_range = [
      iCmp_arg_const r11 0L ;
      IJl "index_too_low" ;
      iCmp_arg_arg r11 (Ptr(R10, 0L)) ;
      IJge "index_too_high"
    ]
    in
    compiled_t @
    (check_rax_is_tuple_instr slot) @
    compiled_pos @
    [
      iMov_arg_arg (rbp_pointer next_slot) rax ; 
      iMov_arg_arg rax (rbp_pointer next_slot)
    ] @
    (check_rax_is_int_instr next_slot) @
    compiled_value @
    [
      iMov_arg_arg (rbp_pointer (Int64.sub next_slot 1L)) rax ;
      iPush r10 ;
      iPush r11 ;
      iMov_arg_arg r10 rbp_ptr ;
      iSub_arg_const r10 1L ;
      iMov_arg_arg r11 (rbp_pointer next_slot) 
    ] @
    check_index_range @
      (*iCmp_arg_const r11 0L ;
      IJl "index_too_low" ;
      iCmp_arg_arg r11 (Ptr(R10, 0L)) ;
      IJge "index_too_high" ;*)
    [
      iSar r11 2L ;
      iAdd_arg_const r11 1L ;
      iSal r11 3L ;
      iAdd_arg_arg r10 r11 ;
      iMov_arg_arg r11 (rbp_pointer (Int64.sub next_slot 1L)) ;
      iMov_arg_arg (Ptr(R10, 0L)) r11 ;
      iPop r11 ;
      iPop r10 ;
      iMov_arg_to_RAX rbp_ptr
    ] 
  in

  (* Main compile instruction here *)
  match e with 
  | TId (s, _) -> compile_tid s
  | TNum (n, _) -> [iMov_const_to_RAX (Int64.mul n add_int_tag)]
  | TBool (b, _) -> [iMov_const_to_RAX (bool_to_int b)]
  | TPrim1 (op, n, _) -> compile_prim1 op n
  | TLet (x, v, e, _) -> compile_let x v e
  | TPrim2 (op, n1, n2, tag) -> compile_prim2 op n1 n2 tag
  | TIf(cond, thn, els, tag) -> compile_if cond thn els tag
  | TApply(nm, args, _) -> compile_apply nm args
  | TTuple(attrs, _) -> compile_tuple attrs 
  | TSet(t, pos, value, _) -> compile_set t pos value 
    
  (*| _ -> failwith "TO BE DONE!"*)

(* Compiles the function definitions. *)
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

(* Prints the program p (given in abstract Scheme syntax) in NASM code. *)
let compile_prog p : string =
  (*Printf.sprintf "%s\n" (string_of_prog p)*)

  (*let _, e = p in*)
  let (tagged_funcs, tagged_main) = tag_prog p in
  let (intrs_funs, cfenv)  = (compile_funcs tagged_funcs (("type_mismatch", [])::empty_comp_fenv)) in 
  let n_lets_main = count_exprs tagged_main in
  let instrs_main = function_start n_lets_main @ compile_expr tagged_main empty_slot_env Int64.minus_one cfenv 0 0 @ function_end in
  let init_heap = "
  mov R15, RDI
  add R15, 7
  mov R11, 0xfffffffffffffff8
  and R15, R11" in
  let prelude ="
section .text
extern check_overflow_add
extern check_overflow_sub
extern check_overflow_mul
extern check_div_by_0
extern typeError
extern indexError
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
  call typeError
error_not_tuple:
  push RSI
  push RDI
  mov RSI, RAX
  mov RDI, 0x3
  call typeError
index_too_high:
  push RSI
  push RDI
  mov RDI, R11
  mov RSI, [R10]
  call indexError
index_too_low:
  push RSI
  push RDI
  mov RDI, R11
  mov RSI, [R10]
  mov RDI, 0
  call indexError" in
  prelude ^ init_heap ^ pp_instrs (instrs_main)^ pp_instrs intrs_funs ^ error_section
