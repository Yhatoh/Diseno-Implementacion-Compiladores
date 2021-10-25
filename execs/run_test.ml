open Dev.Ast
open Dev.Asm
open Dev.Parse
open Dev.Compile
open Dev.Interp
open Alcotest
open Bbctester.Test
open Printf
open Dev.Regsandstack
open Execs.Testentrega3

(* Testing arithmetic expression using the print function defined in Interp 
   and the default equality for comparison *)
let exp : expr testable =
  testable (fun oc e -> Format.fprintf oc "%s" (string_of_expr e)) (=)

let value : value testable =
  testable (fun oc e -> Format.fprintf oc "%s" (string_of_val e)) (=)

let arg : arg testable =
  testable (fun oc e -> Format.fprintf oc "%s" (pp_arg e)) (=)

let instruction : instruction testable =
  testable (fun oc e -> Format.fprintf oc "%s" (pp_instr e)) (=)

let instruction_list : instruction list testable =
  testable (fun oc e -> Format.fprintf oc "%s" (pp_instrs e)) (=)

let tag_expr_t : tag texpr testable =
  testable (fun oc e -> Format.fprintf oc "%s" (string_of_tag_expr e)) (=)


(* Tests for our [parse] function *)
let test_parse_int () =
  check exp "same int" (parse_exp (`Atom "5")) (Num 5L)

let test_parse_var () =
  check exp "same var" (parse_exp (`Atom "x")) (Id "x")

let test_parse_bool () =
  check exp "same bool" (parse_exp (`Atom "true")) (Bool true)
  
let test_parse_tuple () =
    check exp "same tuple" (parse_exp (`List [`Atom "tup"; `Atom "true" ; `Atom "1"])) (Tuple [(Bool true);(Num 1L)] )

let test_parse_add1 () =
  check exp "increment applies" 
  (parse_exp (`List [`Atom "add1" ; `Atom "1"])) 
  (Prim1 (Add1, Num 1L))

let test_parse_sub1 () =
  check exp "decrement applies" 
  (parse_exp (`List [`Atom "sub1" ; `Atom "1"])) 
  (Prim1 (Sub1, Num 1L))
  
let test_parse_add () =
  check exp "addition applies" 
  (parse_exp (`List [`Atom "+" ; `Atom "1" ; `Atom "7"])) 
  (Prim2 (Add, Num 1L, Num 7L))

let test_parse_less () =
  check exp "lesser comparison applies" 
  (parse_exp (`List [`Atom "<=" ; `Atom "1" ; `Atom "7"])) 
  (Prim2 (Lte, Num 1L, Num 7L))

let test_parse_and () =
  check exp "conjunction applies" 
  (parse_exp (`List [`Atom "and" ; `Atom "true" ; `Atom "false"])) 
  (Prim2 (And, Bool true, Bool false))

let test_parse_get () =
    check exp "get applies" (parse_exp (`List [`Atom "get" ; `Atom "1";`Atom "2"])) (Prim2 (Get,Num 1L, Num 2L))

let test_parse_set () =
    check exp "set applies" (parse_exp (`List [`Atom "set" ; `Atom "true";`Atom "37";`Atom "3"])) (Set (Bool true, Num 37L,Num 3L))

let test_parse_fork () =
  check exp "if clause applies"
  (parse_exp (`List [`Atom "if" ; `Atom "true" ; `Atom "1" ; `Atom "0"])) 
  (If (Bool true, Num 1L, Num 0L))

let test_parse_let () =
  check exp "declaration applies"
  (parse_exp (`List [`Atom "let" ; `List [`Atom "x" ; `Atom "1"] ; `List [`Atom "let" ; `List [`Atom "y" ; `Atom "7"] ; `Atom "10"] ])) 
  (Let ("x", Num 1L, Let ("y", Num 7L, Num 10L)))

let test_parse_compound () =
  check exp "same expr"
  (parse_exp (`List [`Atom "+" ; `List [`Atom "+" ; `Atom "3"; `Atom "x"]; `Atom "7"]))
  (Prim2 (Add, Prim2 (Add, Num 3L, Id "x"), Num 7L))

let test_parse_error () =
  let sexp = `List [`List [`Atom "foo"]; `Atom "bar"] in
  check_raises "Should raise a parse error" 
    (CTError (Fmt.strf "Not a valid expr: %a" CCSexp.pp sexp))
    (fun () -> ignore @@ parse_exp sexp)

(* Tests for our [interp] function *)
let test_interp_num () =
  check value "same int" (interp (Num 42L) empty_env empty_fenv) (NumV 42L)

let test_interp_var () =
  check value "same int" (interp (Id "x") (extend_env ["x"] [(NumV 7L)] empty_env) empty_fenv) (NumV 7L)

let test_interp_bool () =
  let v = (interp (Bool true) empty_env empty_fenv) in check value "same bool" v 
  (BoolV true)

let test_interp_add1 () =
  let v = (interp (Prim1 (Add1, Num 1L)) empty_env empty_fenv) in 
  check value "correct increment" v 
  (NumV 2L)

let test_interp_sub1 () =
  let v = (interp (Prim1 (Sub1, Num 1L)) empty_env empty_fenv) in 
  check value "correct decrement" v 
  (NumV 0L)

let test_interp_add () =
  let v = (interp (Prim2 (Add, Num 1L, Num (-1L))) empty_env empty_fenv) in 
  check value "correct addition" v 
  (NumV 0L)

let test_interp_less () =
  let v = (interp (Prim2 (Lte, Num 70L, Num 10L))) empty_env empty_fenv in 
  check value "correct lesser comparison" v 
  (BoolV false)

let test_interp_and () =
  let v = (interp (Prim2 (And, Bool true, Bool false))) empty_env empty_fenv in 
  check value "correct conjunction" v 
  (BoolV false)

let test_interp_fork_1 () =
  let v = (interp (If (Prim2 (Lte, Num 0L, Num 1L), (Num 70L), (Bool false)))) empty_env empty_fenv in 
  check value "correct execution fork true" v 
  (NumV 70L)
  
let test_interp_fork_2 () =
  let v = (interp (If (Prim2 (Lte, Num 1L, Num 0L), (Num 70L), (Bool false)))) empty_env empty_fenv in 
  check value "correct execution fork false" v 
  (BoolV false)
  
let test_interp_let_1 () =
  let v = (interp (Let ("x", Num 1L, (Let ("y", Bool false, (Prim2 (And, Id "y", (Prim2 (Lte, Id "x", Num 0L))))))))) empty_env empty_fenv in
  check value "correct simple variable assignment" v 
  (BoolV false)
  
let test_interp_let_2 () =
  let v = (interp (Let ("x", Num 2L, (Let ("y", (Let ("x", Num 1L, Id "x")), (Prim2 (Add, Id "x", Id "x"))))))) empty_env empty_fenv in
  check value "correct complex variable assignment" v 
  (NumV 4L)

let test_interp_fo_fun_1 () =
  let v = (interp_prog (
    [DefFun ("f", ["x"], (Prim2 (Add, Id "x", Id "x")))],
    (Apply ("f", [Num 2L]))
  )) empty_env in 
  check value "correct simple function execution" v 
  (NumV 4L)

let test_interp_tup () =
  let v = (interp (Tuple [Num 12L;Bool true;Tuple []])) empty_env empty_fenv in
  check value "a tuple val" v 
  (TupleV (ref [NumV 12L;BoolV true; TupleV (ref [])]))

let test_interp_get () =
  let v = (interp (Prim2 (Get ,Tuple [Num 12L;Bool true;Tuple []],Num 0L))) empty_env empty_fenv in
  check value "correct get execution" v 
  (NumV 12L)

let test_interp_set () =
  let v = (interp (Let ("x",(Tuple [Num 12L;Bool true;Tuple []]) , (Let ("foo", (Set (Id "x", Num 1L, Bool false)), (Id "x")))))) empty_env empty_fenv in
  check value "correct set execution" v 
  (TupleV (ref [NumV 12L;BoolV false; TupleV (ref [])]))
  
let test_interp_fo_fun_2 () =
  let v = (interp_prog (
    [DefFun ("f", ["x" ; "y" ; "z"], (Prim2 (Add, (Prim2 (Add, Id "x", Id "y")), Id "z")))],
  (Apply ("f" , [Num 2L ; Num 20L ; Num 200L]))
  )) empty_env in 
  check value "correct complex function execution" v 
  (NumV 222L)
  
let test_interp_fo_app_1 () =
  check value "correct simple function application"
  (NumV 14L)
  (interp_prog ( 
  (
    [
      DefFun ("f", ["x" ; "y"], (Prim2 (Add, Id "x", Id "y")));
      DefFun ("g", ["y"], (Prim2 (Add, Num 7L, Id "y")))
    ],
    (Apply ("g", [
      (Apply ("f", [Num 4L ; Num 3L]))
    ]))
  )
  ) empty_env)

let test_interp_fo_app_2 () =
  check value "correct simple function application"
  (NumV 200L)
  (interp_prog ( 
  (
    [
      DefFun ("f", ["x" ; "y"], (Prim2 (Add, Id "x", Id "y")));
      DefFun ("g", ["x"], (Apply ("f", [Id "x" ; Id "x"])))
    ],
    (Apply ("g", [Num 100L]))
  )
  ) empty_env)

let test_interp_compound () =
  check value "same int"
    (interp (Prim2 (Add, Prim2 (Add, Num 3L, (Prim1 (Sub1, Num 6L))), Num 12L)) empty_env empty_fenv)
    (NumV 20L)

(* Test for our constructor function *)
let test_constructor_rsp_pointer () =
  check arg "same arg"
    (rsp_pointer 2L)
    (Ptr (RSP, 2L))
  
let test_constructor_rbp_pointer () =
  check arg "same arg"
    (rbp_pointer 2L)
    (Ptr (RBP, 2L))

let test_constructor_const () =
  check arg "same arg"
    (const_factory 2L)
    (Const 2L)

let test_constructor_imov_arg_arg () =
  check instruction "same instruction"
    (iMov_arg_arg (Reg RAX) (Ptr(RBP, 2L)))
    (IMov (Reg RAX, Ptr(RBP, 2L)))

let test_constructor_imov_arg_const () =
  check instruction "same instruction"
    (iMov_arg_const (Reg RAX) (1L))
    (IMov (Reg RAX, Const 1L))

let test_constructor_imov_arg_to_RAX () =
  check instruction "same instruction"
    (iMov_arg_to_RAX (Ptr(RBP, 2L)))
    (IMov (Reg RAX, Ptr(RBP, 2L)))

let test_constructor_imov_const_to_RAX () =
  check instruction "same instruction"
    (iMov_const_to_RAX (1L))
    (IMov (Reg RAX, Const 1L))

let test_constructor_iadd_arg_arg () =
  check instruction "same instruction"
    (iAdd_arg_arg (Reg RAX) (Ptr(RBP, 2L)))
    (IAdd (Reg RAX, Ptr(RBP, 2L)))

let test_constructor_iadd_arg_const () =
  check instruction "same instruction"
    (iAdd_arg_const (Reg RAX) (1L))
    (IAdd (Reg RAX, Const 1L))

let test_constructor_iand_arg_arg () =
  check instruction "same instruction"
    (iAnd_arg_arg (Reg RAX) (Ptr(RBP, 2L)))
    (IAnd (Reg RAX, Ptr(RBP, 2L)))

let test_constructor_iand_arg_const () =
  check instruction "same instruction"
    (iAnd_arg_const (Reg RAX) (1L))
    (IAnd (Reg RAX, Const 1L))

let test_constructor_isub_arg_arg () =
  check instruction "same instruction"
    (iSub_arg_arg (Reg RAX) (Ptr(RBP, 2L)))
    (ISub (Reg RAX, Ptr(RBP, 2L)))

let test_constructor_isub_arg_const () =
  check instruction "same instruction"
    (iSub_arg_const (Reg RAX) (3L))
    (ISub (Reg RAX, Const 3L))

let test_constructor_icmp_arg_arg () =
  check instruction "same instruction"
    (iCmp_arg_arg (Reg RAX) (Ptr(RBP, 2L)))
    (ICmp (Reg RAX, Ptr(RBP, 2L)))

let test_constructor_icmp_arg_const () =
  check instruction "same instruction"
    (iCmp_arg_const (Reg RAX) (1L))
    (ICmp (Reg RAX, Const 1L))

let test_constructor_inot_arg () =
  check instruction "same instruction"
    (iNot_arg (Reg RAX))
    (INot (Reg RAX))

let test_constructor_i_jmp () =
  check instruction "same instruction"
    (i_jmp "a_label")
    (IJmp "a_label")

let test_constructor_i_je () =
  check instruction "same instruction"
    (i_je "a_label")
    (IJe "a_label")

let test_constructor_i_jg () =
  check instruction "same instruction"
    (i_jg "a_label")
    (IJg "a_label")

let test_constructor_i_label () =
  check instruction "same instruction"
    (i_label "a_label")
    (ILabel "a_label")

(* Test for our operators to instructions list *)
let test_unop_to_instr_list_add1 () =
  check instruction_list "same instruction_list"
    (unop_to_instr_list Add1)
    ([IAdd (Reg RAX, Const 2L)])

let test_unop_to_instr_list_sub1 () =
  check instruction_list "same instruction_list"
    (unop_to_instr_list Sub1)
    ([ISub (Reg RAX, Const 2L)])
  
let test_unop_to_instr_list_not () =
  check instruction_list "same instruction_list"
    (unop_to_instr_list Not)
    ([INot (Reg RAX) ; IAdd (Reg RAX, Const 1L)])

let test_binop_to_instr_list_add () =
  check instruction_list "same instruction_list"
    (binop_to_instr Add 3L 1 0)
    ([IAdd (Reg RAX, Ptr(RBP, 3L))])

let test_binop_to_instr_list_and () =
  check instruction_list "same instruction_list"
    (binop_to_instr And 3L 1 0)
    ([IAnd (Reg RAX, Ptr(RBP, 3L))])

let test_binop_to_instr_list_lte () =
  check instruction_list "same instruction_list"
    (binop_to_instr Lte 3L 1 0)
    ([ICmp (Reg RAX, Ptr(RBP, 3L))
      ; IJg ("if_false_0_1")
      ; IMov (Reg RAX, Const 3L)
      ; IJmp ("done_0_1")
      ; ILabel ("if_false_0_1")
      ; IMov (Reg RAX, Const 1L)
      ; ILabel ("done_0_1")])

let test_binop_boolean_to_instr_list_and () = 
  check instruction_list "same instruction_list"
    (binop_boolean_to_instr_list [IMov (Ptr (RBP, 1L), Reg RAX); 
                                  IAnd (Reg RAX, Ptr(RBP, 3L)); 
                                  IMov (Ptr (RBP, 2L), Reg RAX);
                                  IMov (Reg RAX, Ptr (RBP, 1L));
                                  IAnd (Reg RAX, Ptr(RBP, 2L))] 1 0 false)
    ([ICmp (Reg RAX, Const 1L); 
      IJe ("skip_0_1");
      IMov (Ptr (RBP, 1L), Reg RAX); 
      IAnd (Reg RAX, Ptr(RBP, 3L)); 
      IMov (Ptr (RBP, 2L), Reg RAX);
      IMov (Reg RAX, Ptr (RBP, 1L));
      IAnd (Reg RAX, Ptr(RBP, 2L));
      ILabel ("skip_0_1")])

let test_lte_op_to_instr_list () =
  check instruction_list "same instruction_list"
    (compile_lte (Reg RAX) (Ptr (RBP, 3L)) (1) 0)
    ([ICmp (Reg RAX, Ptr(RBP, 3L))
      ; IJg ("if_false_0_1")
      ; IMov (Reg RAX, Const 3L)
      ; IJmp ("done_0_1")
      ; ILabel ("if_false_0_1")
      ; IMov (Reg RAX, Const 1L)
      ; ILabel ("done_0_1")])

(* Test for our [tag] function *)
let test_tag_num () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Num 1L))
    (TNum (1L, 1))

let test_tag_bool () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Bool true))
    (TBool (true, 1))

let test_tag_id () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Id "x"))
    (TId ("x", 1))

let test_tag_add1 () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Prim1 (Add1, Num 1L)))
    (TPrim1 (Add1, (TNum (1L, 2)), 1))

let test_tag_sub1 () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Prim1 (Sub1, Num 1L)))
    (TPrim1 (Sub1, (TNum (1L, 2)), 1))

let test_tag_not () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Prim1 (Not, Bool true)))
    (TPrim1 (Not, (TBool (true, 2)), 1))

let test_tag_add () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Prim2 (Add, Num 4L, Num 2L)))
    (TPrim2 (Add, (TNum (4L, 2)), (TNum (2L, 3)), 1))

let test_tag_and () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Prim2 (And, Bool true, Bool true)))
    (TPrim2 (And, (TBool (true, 2)), (TBool (true, 3)), 1))

let test_tag_lte () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Prim2 (Lte, Num 4L, Num 2L)))
    (TPrim2 (Lte, (TNum (4L, 2)), (TNum (2L, 3)), 1))

let test_tag_let () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Let ("x", Num 4L, Prim2 (Add, Id "x", Num 2L))))
    (TLet ("x", (TNum (4L, 2)), TPrim2 (Add, (TId ("x", 4)), (TNum (2L, 5)), 3), 1))

let test_tag_if () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (If (Bool true, Num 4L, Prim2 (Add, Id "x", Num 2L))))
    (TIf 
      ((TBool (true, 2)), 
        (TNum (4L, 3)), 
        (TPrim2 (Add, (TId ("x", 5)), (TNum (2L, 6)), 4)), 
      1))

let test_tag_compound () = 
  check tag_expr_t "same tag_expr_t"
    (tag_expr (Let 
          (("x"), (Bool true), 
           (Let 
            (("y"), (Num 10L), 
              (If 
                ((Prim2(And, Prim2(Lte, Num 20L, Id "x"), (Id "x"))), 
                (Num 100L),
                (Bool true))))
            )
           )
          )
         )
    (TLet
      ("x",
       (TBool (true, 2)),
       (TLet
        ("y", 
         (TNum (10L, 4)), 
         (TIf
          ((TPrim2 
            (And, 
              (TPrim2 
                (Lte, 
                 (TNum (20L, 8)), 
                 (TId ("x", 9)), 
                7)), 
              (TId ("x", 10)), 
              6)), 
           (TNum (100L, 11)), 
           (TBool (true, 12)), 
           5)),
        3)), 
      1)) 

(* Test our [compile expr] function *)
let test_compile_num () = 
  check instruction_list "same instruction_list"
    (compile_expr (TNum (1L, 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 2L)])

let test_compile_bool () = 
  check instruction_list "same instruction_list"
    (compile_expr (TBool (true, 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 3L)])

let test_check_rax_is_type_int () =
  check instruction_list "same instruction_list"
    (check_rax_is_type_instr 0L 1L)
    ([
      IMov (Ptr (RBP, 1L), Reg RAX) ;
      IAnd (Reg RAX, Const 1L) ;
      ICmp (Reg RAX, Const 0L) ;
      IMov (Reg RAX, Ptr (RBP, 1L)) ;
      IJne ("error_not_number")
    ])

let test_check_rax_is_type_bool () =
  check instruction_list "same instruction_list"
    (check_rax_is_type_instr 1L 1L)
    ([
      IMov (Ptr (RBP, 1L), Reg RAX) ;
      IAnd (Reg RAX, Const 1L) ;
      ICmp (Reg RAX, Const 1L) ;
      IMov (Reg RAX, Ptr (RBP, 1L)) ;
      IJne "error_not_boolean"
    ])


let test_compile_print_int () =
  check instruction_list "same instruction_list"
    (compile_expr (tag_expr (Prim1 (Print, Num 2L))) empty_slot_env Int64.minus_one [] 0 0)
    ([
      IMov (Reg RAX, Const 4L) ;
      IPush (Reg RDI) ;
      IMov (Reg RDI, Reg RAX) ;
      ICall "print" ;
      IPop (Reg RDI)
    ])
  
let test_compile_print_bool () =
  check instruction_list "same instruction_list"
    (compile_expr (tag_expr (Prim1 (Print, Bool true))) empty_slot_env Int64.minus_one [] 0 0)
    ([
      IMov (Reg RAX, Const 3L) ;
      IPush (Reg RDI) ;
      IMov (Reg RDI, Reg RAX) ;
      ICall "print" ;
      IPop (Reg RDI)
    ])
  
let test_compile_func_def () =
  check instruction_list "same instruction_list"
    (let (f_list, _) = (compile_funcs (tag_funs [(DefFun ("f", ["x"], Id "x"))] 1) empty_comp_fenv) in
      f_list)
    ([
      ILabel "f" ;
      IPush (Reg RBP) ;
      IMov (Reg RBP, Reg RSP) ;
      ISub (Reg RSP, Const 8L) ;
      IMov (Reg RAX, Reg RDI) ;
      IMov (Reg RSP, Reg RBP) ;
      IPop (Reg RBP);
      IRet
    ])

let test_compile_func_app () =
  check instruction_list "same instruction_list"
    (compile_expr (tag_expr ((Apply ("f", [(Num 1L)])))) empty_slot_env Int64.minus_one [("f", ["x"])] 0 0)
    ([
      IPush (Reg R9) ;
      IPush (Reg R8) ;
      IPush (Reg RCX) ;
      IPush (Reg RDX) ;
      IPush (Reg RSI) ;
      IPush (Reg RDI) ;
      IMov (Reg RAX, Const 2L) ;
      IMov (Reg RDI, Reg RAX) ;
      ICall "f" ;
      IPop (Reg RDI) ;
      IPop (Reg RSI) ;
      IPop (Reg RDX) ;
      IPop (Reg RCX) ;
      IPop (Reg R8) ;
      IPop (Reg R9) ;
    ])


let test_compile_add1 () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim1 (Add1, (TNum (1L, 2)), 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 2L)] @
    check_rax_is_type_instr 0L Int64.minus_one @
    [
      IMov (Ptr (RBP, Int64.minus_one), Reg RAX) ;
      IPush (Reg RSI) ;
      IPush (Reg RDI) ;
      IMov (Reg RDI, Reg RAX) ;
      IMov (Reg RSI, Const 2L) ;
      ICall "check_overflow_add" ;
      IPop (Reg RDI) ;
      IPop (Reg RSI) ;
      IMov (Reg RAX, Ptr (RBP, Int64.minus_one))
    ] @ [IAdd (Reg RAX, Const 2L)])

let test_compile_sub1 () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim1 (Sub1, (TNum (1L, 2)), 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 2L)] @
    check_rax_is_type_instr 0L Int64.minus_one @
    [
      IMov (Ptr (RBP, Int64.minus_one), Reg RAX) ;
      IPush (Reg RSI) ;
      IPush (Reg RDI) ;
      IMov (Reg RDI, Reg RAX) ;
      IMov (Reg RSI, Const 2L) ;
      ICall "check_overflow_sub" ;
      IPop (Reg RDI) ;
      IPop (Reg RSI) ;
      IMov (Reg RAX, Ptr (RBP, Int64.minus_one))
    ] @ [ISub (Reg RAX, Const 2L)])

let test_compile_not () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim1 (Not, (TBool (false, 2)), 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 1L)] @
    check_rax_is_type_instr 1L Int64.minus_one @
    [INot (Reg RAX) ; IAdd (Reg RAX, Const 1L)])

let test_compile_add () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim2 (Add, (TNum (4L, 2)), (TNum (2L, 3)), 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 8L)] @
      check_rax_is_type_instr 0L Int64.minus_one @
      [IMov (Ptr (RBP, Int64.minus_one), Reg RAX); 
      IMov (Reg RAX, Const 4L)] @
      check_rax_is_type_instr 0L (Int64.sub 0L 2L) @
      [IMov (Ptr (RBP, (Int64.sub 0L 2L)), Reg RAX)] @
      [
        IPush (Reg RSI) ;
        IPush (Reg RDI) ;
        IMov (Reg RDI, Ptr (RBP, Int64.minus_one)) ;
        IMov (Reg RSI, Ptr (RBP, (Int64.sub 0L 2L))) ;
        ICall "check_overflow_add" ;
        IPop (Reg RDI) ;
        IPop (Reg RSI) ;
        IMov (Reg RAX, Ptr (RBP, Int64.minus_one))
      ] @
      [IAdd (Reg RAX, Ptr (RBP, (Int64.sub 0L 2L)));
     ])

let test_compile_sub () = 
check instruction_list "same instruction_list"
  (compile_expr (TPrim2 (Sub, (TNum (4L, 2)), (TNum (2L, 3)), 1)) empty_slot_env Int64.minus_one [] 0 0)
  ([IMov (Reg RAX, Const 8L)] @
    check_rax_is_type_instr 0L Int64.minus_one @
    [IMov (Ptr (RBP, Int64.minus_one), Reg RAX); 
    IMov (Reg RAX, Const 4L)] @
    check_rax_is_type_instr 0L (Int64.sub 0L 2L) @
    [IMov (Ptr (RBP, (Int64.sub 0L 2L)), Reg RAX)] @
    [
      IPush (Reg RSI) ;
      IPush (Reg RDI) ;
      IMov (Reg RDI, Ptr (RBP, Int64.minus_one)) ;
      IMov (Reg RSI, Ptr (RBP, (Int64.sub 0L 2L))) ;
      ICall "check_overflow_sub" ;
      IPop (Reg RDI) ;
      IPop (Reg RSI) ;
      IMov (Reg RAX, Ptr (RBP, Int64.minus_one))
    ] @
    [ISub (Reg RAX, Ptr (RBP, (Int64.sub 0L 2L)));
    ])

let test_compile_mul () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim2 (Mul, (TNum (4L, 2)), (TNum (2L, 3)), 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 8L)] @
      check_rax_is_type_instr 0L Int64.minus_one @
      [IMov (Ptr (RBP, Int64.minus_one), Reg RAX); 
      IMov (Reg RAX, Const 4L)] @
      check_rax_is_type_instr 0L (Int64.sub 0L 2L) @
      [IMov (Ptr (RBP, (Int64.sub 0L 2L)), Reg RAX)] @
      [
        IPush (Reg RSI) ;
        IPush (Reg RDI) ;
        IMov (Reg RDI, Ptr (RBP, Int64.minus_one)) ;
        IMov (Reg RSI, Ptr (RBP, (Int64.sub 0L 2L))) ;
        ICall "check_overflow_mul" ;
        IPop (Reg RDI) ;
        IPop (Reg RSI) ;
        IMov (Reg RAX, Ptr (RBP, Int64.minus_one))
      ] @
      [IMul (Reg RAX, Ptr (RBP, (Int64.sub 0L 2L)));
       ISar (Reg RAX, Const 1L);
      ])

let test_compile_div () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim2 (Div, (TNum (4L, 2)), (TNum (2L, 3)), 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 8L)] @
      check_rax_is_type_instr 0L Int64.minus_one @
      [IMov (Ptr (RBP, Int64.minus_one), Reg RAX); 
      IMov (Reg RAX, Const 4L)] @
      check_rax_is_type_instr 0L (Int64.sub 0L 2L) @
      [IMov (Ptr (RBP, (Int64.sub 0L 2L)), Reg RAX)] @
      [
        IPush (Reg RSI) ;
        IPush (Reg RDI) ;
        IMov (Reg RDI, Ptr (RBP, (Int64.sub 0L 2L))) ;
        ICall "check_div_by_0" ;
        IPop (Reg RDI) ;
        IPop (Reg RSI) ;
        IMov (Reg RAX, Ptr (RBP, Int64.minus_one))
      ] @
      [IDiv (Reg RAX, Ptr (RBP, (Int64.sub 0L 2L)));
        ISal (Reg RAX, Const 1L);
      ])

let test_compile_and () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim2 (And, (TBool (true, 2)), (TBool (true, 3)), 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 3L)] @
      check_rax_is_type_instr 1L Int64.minus_one @
      [ICmp (Reg RAX, Const 1L);
      IJe ("skip_0_1");
      IMov (Ptr (RBP, Int64.minus_one), Reg RAX); 
      IMov (Reg RAX, Const 3L)] @
      check_rax_is_type_instr 1L (Int64.sub 0L 2L) @
      [IMov (Ptr (RBP, (Int64.sub 0L 2L)), Reg RAX);
      IMov (Reg RAX, Ptr (RBP, Int64.minus_one));
      IAnd (Reg RAX, Ptr (RBP, (Int64.sub 0L 2L)));
      ILabel ("skip_0_1")
     ])

let test_compile_lte () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim2 (Lte, (TNum (4L, 2)), (TNum (2L, 3)), 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 8L)] @
      check_rax_is_type_instr 0L Int64.minus_one @
      [IMov (Ptr (RBP, Int64.minus_one), Reg RAX); 
      IMov (Reg RAX, Const 4L)] @
      check_rax_is_type_instr 0L (Int64.sub 0L 2L) @
      [IMov (Ptr (RBP, (Int64.sub 0L 2L)), Reg RAX);
      IMov (Reg RAX, Ptr (RBP, Int64.minus_one));
      ICmp (Reg RAX, Ptr (RBP, (Int64.sub 0L 2L)));
      IJg ("if_false_0_1");
      IMov (Reg RAX, Const 3L);
      IJmp ("done_0_1");
      ILabel ("if_false_0_1");
      IMov (Reg RAX, Const 1L);
      ILabel ("done_0_1")
     ])

let test_compile_let () = 
  check instruction_list "same instruction_list"
    (compile_expr (TLet ("x", (TNum (4L, 2)), TPrim2 (Add, (TId ("x", 4)), (TNum (2L, 5)), 3), 1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 8L);
      IMov (Ptr (RBP, Int64.minus_one), Reg RAX);
      IMov (Reg RAX, Ptr(RBP, Int64.minus_one))] @
      check_rax_is_type_instr 0L (Int64.sub 0L 2L) @
      [IMov (Ptr (RBP, (Int64.sub 0L 2L)), Reg RAX); 
      IMov (Reg RAX, Const 4L)] @
      check_rax_is_type_instr 0L (Int64.sub 0L 3L) @
      [IMov (Ptr (RBP, (Int64.sub 0L 3L)), Reg RAX)] @
      [
        IPush (Reg RSI) ;
        IPush (Reg RDI) ;
        IMov (Reg RDI, Ptr (RBP, (Int64.sub 0L 2L))) ;
        IMov (Reg RSI, Ptr (RBP, (Int64.sub 0L 3L))) ;
        ICall "check_overflow_add" ;
        IPop (Reg RDI) ;
        IPop (Reg RSI) ;
      ] @
      [IMov (Reg RAX, Ptr (RBP, (Int64.sub 0L 2L))); 
      IAdd (Reg RAX, Ptr (RBP, (Int64.sub 0L 3L)));
     ])

let test_compile_if () = 
  check instruction_list "same instruction_list"
    (compile_expr 
      (TIf 
        ((TBool (true, 2)), 
          (TNum (4L, 3)), 
          (TPrim2 (Add, (TNum (4L, 2)), (TNum (2L, 3)), 1)), 
          1)
        )
      empty_slot_env Int64.minus_one [] 0 0
    )
    ([IMov (Reg RAX, Const 3L)] @
      check_rax_is_type_instr 1L Int64.minus_one @
      [ICmp (Reg RAX, Const 1L);
      IJe ("if_false_0_1");
      IMov (Reg RAX, Const 8L);
      IJmp ("done_0_1");
      ILabel ("if_false_0_1");
      IMov (Reg RAX, Const 8L)] @
      check_rax_is_type_instr 0L Int64.minus_one @
      [IMov (Ptr (RBP, Int64.minus_one), Reg RAX); 
      IMov (Reg RAX, Const 4L)] @
      check_rax_is_type_instr 0L (Int64.sub 0L 2L) @
      [IMov (Ptr (RBP, (Int64.sub 0L 2L)), Reg RAX)] @
      [
        IPush (Reg RSI) ;
        IPush (Reg RDI) ;
        IMov (Reg RDI, Ptr (RBP, Int64.minus_one)) ;
        IMov (Reg RSI, Ptr (RBP, (Int64.sub 0L 2L))) ;
        ICall "check_overflow_add" ;
        IPop (Reg RDI) ;
        IPop (Reg RSI) ;
      ] @
      [IMov (Reg RAX, Ptr (RBP, Int64.minus_one));
      IAdd (Reg RAX, Ptr (RBP, (Int64.sub 0L 2L)));
      ILabel ("done_0_1");
     ])

let test_compile_compound () = 
  check instruction_list "same instruction_list"
    (compile_expr
      (TLet
        ("x",
         (TBool (true, 2)),
         (TLet
          ("y", 
           (TNum (10L, 4)), 
           (TIf
            ((TPrim2 
              (And, 
                (TPrim2 
                  (Lte, 
                   (TNum (20L, 8)), 
                   (TId ("x", 9)), 
                  7)), 
                (TId ("x", 10)), 
                6)), 
             (TNum (100L, 11)), 
             (TBool (true, 12)), 
             5)),
          3)), 
        1)) empty_slot_env Int64.minus_one [] 0 0)
    ([IMov (Reg RAX, Const 3L);
      IMov (Ptr(RBP, Int64.minus_one), Reg RAX);
      IMov (Reg RAX, Const 20L);
      IMov (Ptr(RBP, (Int64.sub 0L 2L)), Reg RAX);
      IMov (Reg RAX, Const 40L)] @
      check_rax_is_type_instr 0L (Int64.sub 0L 3L) @
      [IMov (Ptr(RBP, (Int64.sub 0L 3L)), Reg RAX);
      IMov (Reg RAX, Ptr (RBP, Int64.minus_one))] @
      check_rax_is_type_instr 0L (Int64.sub 0L 4L) @
      [IMov (Ptr(RBP, (Int64.sub 0L 4L)), Reg RAX);
      IMov (Reg RAX, Ptr (RBP, (Int64.sub 0L 3L)));
      ICmp (Reg RAX, Ptr (RBP, (Int64.sub 0L 4L)));
      IJg ("if_false_0_7");
      IMov (Reg RAX, Const 3L);
      IJmp ("done_0_7");
      ILabel ("if_false_0_7");
      IMov (Reg RAX, Const 1L);
      ILabel ("done_0_7")] @
      check_rax_is_type_instr 1L (Int64.sub 0L 3L) @
      [ICmp (Reg RAX, Const 1L);
      IJe ("skip_0_6");
      IMov (Ptr(RBP, (Int64.sub 0L 3L)), Reg RAX);
      IMov (Reg RAX, Ptr (RBP, Int64.minus_one))] @
      check_rax_is_type_instr 1L (Int64.sub 0L 4L) @
      [IMov (Ptr (RBP, (Int64.sub 0L 4L)), Reg RAX);
      IMov (Reg RAX, Ptr (RBP, (Int64.sub 0L 3L)));
      IAnd (Reg RAX, Ptr (RBP, (Int64.sub 0L 4L)));
      ILabel ("skip_0_6")] @
      check_rax_is_type_instr 1L (Int64.sub 0L 3L) @
      [ICmp (Reg RAX, Const 1L);
      IJe ("if_false_0_5");
      IMov (Reg RAX, Const 200L);
      IJmp ("done_0_5");
      ILabel ("if_false_0_5");
      IMov (Reg RAX, Const 3L);
      ILabel ("done_0_5");
     ])

let test_error_III () =
  let v = (fun () -> ignore @@ interp (Prim2 (Add, Bool true,  Num (-1L))) empty_env empty_fenv) in 
  check_raises "incorrect addition" 
  (RTError "Expected two integers, but got true and -1") v


let test_error_BBB () =
  let v = (fun () -> ignore @@ (interp (Prim2 (And, Num 5L, Bool false))) empty_env empty_fenv) in 
  check_raises "incorrect conjunction"
  (RTError "Expected two booleans, but got 5 and false") v

let test_error_IIB () =
  let v = (fun () -> ignore @@ (interp (Prim2 (Lte, Bool true, Num 10L))) empty_env empty_fenv) in 
  check_raises  "incorrect lesser comparison" 
  (RTError "Expected two integers, but got true and 10") v


(* OCaml tests: extend with your own tests *)
let ocaml_tests = [
  "parse", [
    test_case "A number" `Quick test_parse_int ;
    test_case "A variable" `Quick test_parse_var ;
    test_case "A boolean" `Quick test_parse_bool ;
    test_case "A tuple" `Quick test_parse_tuple ;
    test_case "An increment" `Quick test_parse_add1 ;
    test_case "A decrement" `Quick test_parse_sub1 ;
    test_case "An addition" `Quick test_parse_add ;
    test_case "A get" `Quick test_parse_get ;
    test_case "An set" `Quick test_parse_set ;
    test_case "A lesser comparison" `Quick test_parse_less ;
    test_case "A conjunction" `Quick test_parse_and ;
    test_case "An if clause" `Quick test_parse_fork ;
    test_case "A definition" `Quick test_parse_let ;
    test_case "A compound expression" `Quick test_parse_compound ;
    test_case "An invalid s-expression" `Quick test_parse_error ;

    test_case "A record definition" `Quick test_parse_record ;
  ] ;
  "interp", [
    test_case "A number" `Quick test_interp_num ;
    test_case "A variable" `Quick test_interp_var ;
    test_case "A boolean" `Slow test_interp_bool ;
    test_case "A tuple" `Slow test_interp_tup ;
    test_case "An increment" `Slow test_interp_add1 ;
    test_case "An decrement" `Slow test_interp_sub1 ;
    test_case "An addition" `Slow test_interp_add ;
    test_case "A lesser comparison" `Slow test_interp_less ;
    test_case "A conjunction" `Slow test_interp_and ;
    test_case "An if clause when true" `Slow test_interp_fork_1 ;
    test_case "An if clause when false" `Slow test_interp_fork_2 ;
    test_case "A simple definition" `Slow test_interp_let_1 ;
    test_case "A complex definition" `Slow test_interp_let_2 ;
    test_case "A simple function" `Slow test_interp_fo_fun_1 ;
    test_case "A complex function" `Slow test_interp_fo_fun_2 ;
    test_case "A simple application" `Slow test_interp_fo_app_1 ;
    test_case "A complex application" `Slow test_interp_fo_app_2 ;
    test_case "A compound expression" `Quick test_interp_compound;
    test_case "A get expression" `Slow test_interp_get ;
    test_case "A set expression" `Slow test_interp_set 
  ] ;
  "constructor", [
    test_case "A stack pointer constructor" `Quick test_constructor_rsp_pointer ;
    test_case "A base pointer constructor" `Quick test_constructor_rbp_pointer ;
    test_case "A const constructor" `Quick test_constructor_const ;
    test_case "A mov arg to arg constructor" `Quick test_constructor_imov_arg_arg;
    test_case "A mov const to arg constructor" `Quick test_constructor_imov_arg_const;
    test_case "A mov arg to RAX constructor" `Quick test_constructor_imov_arg_to_RAX;
    test_case "A mov const to RAX constructor" `Quick test_constructor_imov_const_to_RAX;
    test_case "An add arg to arg constructor" `Quick test_constructor_iadd_arg_arg;
    test_case "An add const to arg constructor" `Quick test_constructor_iadd_arg_const;
    test_case "An and arg to arg constructor" `Quick test_constructor_iand_arg_arg;
    test_case "An and const to arg constructor" `Quick test_constructor_iand_arg_const;
    test_case "A sub arg to arg constructor" `Quick test_constructor_isub_arg_arg;
    test_case "A sub const to arg constructor" `Quick test_constructor_isub_arg_const;
    test_case "A cmp arg to arg constructor" `Quick test_constructor_icmp_arg_arg;
    test_case "A cmp const to arg constructor" `Quick test_constructor_icmp_arg_const;
    test_case "A not constructor from an arg" `Quick test_constructor_inot_arg;
    test_case "A jmp constructor" `Quick test_constructor_i_jmp;
    test_case "A je constructor" `Quick test_constructor_i_je;
    test_case "A jg constructor" `Quick test_constructor_i_jg;
    test_case "A label constructor" `Quick test_constructor_i_label;
  ];
  "operators_to_instr_list", [
    test_case "A add1 operation to instr list" `Quick test_unop_to_instr_list_add1;
    test_case "A sub1 operation to instr list" `Quick test_unop_to_instr_list_sub1;
    test_case "A not operation to instr list" `Quick test_unop_to_instr_list_not;
    test_case "A + operation to instr list" `Quick test_binop_to_instr_list_add;
    test_case "A && operation to instr list" `Quick test_binop_to_instr_list_and;
    test_case "A <= operation to instr list" `Quick test_binop_to_instr_list_lte;
    test_case "A <= instruction list" `Quick test_lte_op_to_instr_list;
    test_case "A boolean operation skip instruction list" `Quick test_binop_boolean_to_instr_list_and;
  ];
  "tagging", [
    test_case "Tag a num" `Quick test_tag_num;
    test_case "Tag a bool" `Quick test_tag_bool;
    test_case "Tag a id" `Quick test_tag_id;
    test_case "Tag a add1" `Quick test_tag_add1;
    test_case "Tag a sub1" `Quick test_tag_sub1;
    test_case "Tag a not" `Quick test_tag_not;
    test_case "Tag a +" `Quick test_tag_add;
    test_case "Tag a &&" `Quick test_tag_and;
    test_case "Tag a <=" `Quick test_tag_lte;
    test_case "Tag a let" `Quick test_tag_let;
    test_case "Tag a if" `Quick test_tag_if;

    test_case "Tag a tuple" `Quick test_tag_tup;
    test_case "Tag a tuple get" `Quick test_tag_get;
    test_case "Tag a tuple set" `Quick test_tag_set;
    
    test_case "Tag a compound expression" `Quick test_tag_compound;
  ];
  "compile", [
    test_case "compile a num" `Quick test_compile_num;
    test_case "compile a bool" `Quick test_compile_bool;
    test_case "int type checking" `Quick test_check_rax_is_type_int;
    test_case "bool type checking" `Quick test_check_rax_is_type_bool;
    test_case "compile an add1" `Quick test_compile_add1;
    test_case "compile a sub1" `Quick test_compile_sub1;
    test_case "compile a not" `Quick test_compile_not;
    test_case "compile a +" `Quick test_compile_add;
    test_case "compile a -" `Quick test_compile_sub;
    test_case "compile a *" `Quick test_compile_mul;
    test_case "compile a /" `Quick test_compile_div;
    test_case "compile a &&" `Quick test_compile_and;
    test_case "compile a <=" `Quick test_compile_lte;
    test_case "compile a let" `Quick test_compile_let;
    test_case "compile an if" `Quick test_compile_if;
    test_case "compile a compound" `Quick test_compile_compound;
    test_case "compile a print of int" `Quick test_compile_print_int;
    test_case "compile a print of bool" `Quick test_compile_print_bool;
    test_case "compile a function definition" `Quick test_compile_func_def;
    test_case "compile a function application" `Quick test_compile_func_app ;
    
    test_case "compile a tuple definition" `Quick test_compile_tup ;
    test_case "compile a tuple get" `Quick test_compile_get ;
    test_case "compile a tuple set" `Quick test_compile_set ;
  ];
  "errors", [
    test_case "Addition of true" `Quick test_error_III ;
    test_case "And of 5" `Quick test_error_BBB ;
    test_case "Lesser than true" `Quick test_error_IIB
  ]
]     

(* Entry point of tester *)
let () =
  (* BBC tests: don't change the following, simply add .bbc files in the bbctests/ directory *)
  let bbc_tests = 
    let compile_flags = Option.value (Sys.getenv_opt "CFLAGS") ~default:"-g" in
    let compiler : string -> out_channel -> unit = 
      fun s o -> fprintf o "%s" (compile_prog (parse_prog (sexp_from_string s))) in
    let oracle : string -> status * string = (
      fun s -> (
        try
          NoError, string_of_val (interp_prog (parse_prog (sexp_from_string s)) empty_env)
        with
        | RTError msg -> RTError, msg
        | CTError msg -> CTError, msg
        |  e -> RTError, "Oracle raised an unknown error :"^ Printexc.to_string e 
      )
    ) in
    tests_from_dir ~compile_flags ~compiler ~oracle ~runtime:"rt/sys.c" "bbctests" in
  run "Tests entrega 1" (ocaml_tests @ bbc_tests)
