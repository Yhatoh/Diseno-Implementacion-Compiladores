open Dev.Ast
open Dev.Asm
open Dev.Parse
open Dev.Interp
open Dev.Compile
open Alcotest
open Bbctester.Test
open Printf

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

let tag_expr : tag texpr testable =
  testable (fun oc e -> Format.fprintf oc "%s" (string_of_tag_expr e)) (=)


(* Tests for our [parse] function *)
let test_parse_int () =
  check exp "same int" (parse_exp (`Atom "5")) (Num 5L)

let test_parse_var () =
  check exp "same var" (parse_exp (`Atom "x")) (Id "x")

let test_parse_compound () =
  check exp "same expr"
    (parse_exp (`List [`Atom "+" ; `List [`Atom "+" ; `Atom "3"; `Atom "x"]; `Atom "7"]))
    (Prim2 (Add, Prim2 (Add, Num 3L, Id "x"), Num 7L))

let test_parse_error () =
  let sexp = `List [`Atom "foo"; `Atom "bar"] in
  check_raises "Should raise failwith" 
    (Failure (Fmt.strf "Not a valid expr: %a" CCSexp.pp sexp))
    (fun () -> ignore @@ parse_exp sexp)

(* Tests for our [interp] function *)
let test_interp_num () =
  check value "same int" (interp (Num 42L) empty_env) (NumV 42L)

let test_interp_var () =
  check value "same int" (interp (Id "x") ["x", NumV 7L]) (NumV 7L)

let test_interp_compound () =
  check value "same int"
    (interp (Prim2 (Add, Prim2 (Add, Num 3L, Num 5L), Num 12L)) empty_env)
    (NumV 20L)

(* Test for our constructor function *)
let test_constructor_rsp_pointer () =
  check arg "same arg"
    (rsp_pointer 2L)
    (StackPtr (RSP, 2L))

let test_constructor_const () =
  check arg "same arg"
    (const_factory 2L)
    (Const 2L)

let test_constructor_imov_arg_arg () =
  check instruction "same instruction"
    (iMov_arg_arg (Reg RAX) (StackPtr(RSP, 2L)))
    (IMov (Reg RAX, StackPtr(RSP, 2L)))

let test_constructor_imov_arg_const () =
  check instruction "same instruction"
    (iMov_arg_const (Reg RAX) (1L))
    (IMov (Reg RAX, Const 1L))

let test_constructor_imov_arg_to_RAX () =
  check instruction "same instruction"
    (iMov_arg_to_RAX (StackPtr(RSP, 2L)))
    (IMov (Reg RAX, StackPtr(RSP, 2L)))

let test_constructor_imov_const_to_RAX () =
  check instruction "same instruction"
    (iMov_const_to_RAX (1L))
    (IMov (Reg RAX, Const 1L))

let test_constructor_iadd_arg_arg () =
  check instruction "same instruction"
    (iAdd_arg_arg (Reg RAX) (StackPtr(RSP, 2L)))
    (IAdd (Reg RAX, StackPtr(RSP, 2L)))

let test_constructor_iadd_arg_const () =
  check instruction "same instruction"
    (iAdd_arg_const (Reg RAX) (1L))
    (IAdd (Reg RAX, Const 1L))

let test_constructor_iand_arg_arg () =
  check instruction "same instruction"
    (iAnd_arg_arg (Reg RAX) (StackPtr(RSP, 2L)))
    (IAnd (Reg RAX, StackPtr(RSP, 2L)))

let test_constructor_iand_arg_const () =
  check instruction "same instruction"
    (iAnd_arg_const (Reg RAX) (1L))
    (IAnd (Reg RAX, Const 1L))

let test_constructor_isub_arg_arg () =
  check instruction "same instruction"
    (iSub_arg_arg (Reg RAX) (StackPtr(RSP, 2L)))
    (ISub (Reg RAX, StackPtr(RSP, 2L)))

let test_constructor_isub_arg_const () =
  check instruction "same instruction"
    (iSub_arg_const (Reg RAX) (3L))
    (ISub (Reg RAX, Const 3L))

let test_constructor_icmp_arg_arg () =
  check instruction "same instruction"
    (iCmp_arg_arg (Reg RAX) (StackPtr(RSP, 2L)))
    (ICmp (Reg RAX, StackPtr(RSP, 2L)))

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
    (binop_to_instr Add 3L 1)
    ([IAdd (Reg RAX, StackPtr(RSP, 3L))])

let test_binop_to_instr_list_and () =
  check instruction_list "same instruction_list"
    (binop_to_instr And 3L 1)
    ([IAnd (Reg RAX, StackPtr(RSP, 3L))])

let test_binop_to_instr_list_lte () =
  check instruction_list "same instruction_list"
    (binop_to_instr Lte 3L 1)
    ([ICmp (Reg RAX, StackPtr(RSP, 3L))
      ; IJg ("if_false_1")
      ; IMov (Reg RAX, Const 3L)
      ; IJmp ("done_1")
      ; ILabel ("if_false_1")
      ; IMov (Reg RAX, Const 1L)
      ; ILabel ("done_1")])

let test_binop_boolean_to_instr_list_and () = 
  check instruction_list "same instruction_list"
    (binop_boolean_to_instr_list [IMov (StackPtr (RSP, 1L), Reg RAX); 
                                  IAnd (Reg RAX, StackPtr(RSP, 3L)); 
                                  IMov (StackPtr (RSP, 2L), Reg RAX);
                                  IMov (Reg RAX, StackPtr (RSP, 1L));
                                  IAnd (Reg RAX, StackPtr(RSP, 2L))] 1 false)
    ([ICmp (Reg RAX, Const 1L); 
      IJe ("skip_1");
      IMov (StackPtr (RSP, 1L), Reg RAX); 
      IAnd (Reg RAX, StackPtr(RSP, 3L)); 
      IMov (StackPtr (RSP, 2L), Reg RAX);
      IMov (Reg RAX, StackPtr (RSP, 1L));
      IAnd (Reg RAX, StackPtr(RSP, 2L));
      ILabel ("skip_1")])

let test_lte_op_to_instr_list () =
  check instruction_list "same instruction_list"
    (compile_lte (Reg RAX) (StackPtr (RSP, 3L)) (1))
    ([ICmp (Reg RAX, StackPtr(RSP, 3L))
      ; IJg ("if_false_1")
      ; IMov (Reg RAX, Const 3L)
      ; IJmp ("done_1")
      ; ILabel ("if_false_1")
      ; IMov (Reg RAX, Const 1L)
      ; ILabel ("done_1")])

(* Test for our [tag] function *)
let test_tag_num () = 
  check tag_expr "same tag_expr"
    (tag (Num 1L))
    (TNum (1L, 1))

let test_tag_bool () = 
  check tag_expr "same tag_expr"
    (tag (Bool true))
    (TBool (true, 1))

let test_tag_id () = 
  check tag_expr "same tag_expr"
    (tag (Id "x"))
    (TId ("x", 1))

let test_tag_add1 () = 
  check tag_expr "same tag_expr"
    (tag (Prim1 (Add1, Num 1L)))
    (TPrim1 (Add1, (TNum (1L, 2)), 1))

let test_tag_sub1 () = 
  check tag_expr "same tag_expr"
    (tag (Prim1 (Sub1, Num 1L)))
    (TPrim1 (Sub1, (TNum (1L, 2)), 1))

let test_tag_not () = 
  check tag_expr "same tag_expr"
    (tag (Prim1 (Not, Bool true)))
    (TPrim1 (Not, (TBool (true, 2)), 1))

let test_tag_add () = 
  check tag_expr "same tag_expr"
    (tag (Prim2 (Add, Num 4L, Num 2L)))
    (TPrim2 (Add, (TNum (4L, 2)), (TNum (2L, 3)), 1))

let test_tag_and () = 
  check tag_expr "same tag_expr"
    (tag (Prim2 (And, Bool true, Bool true)))
    (TPrim2 (And, (TBool (true, 2)), (TBool (true, 3)), 1))

let test_tag_lte () = 
  check tag_expr "same tag_expr"
    (tag (Prim2 (Lte, Num 4L, Num 2L)))
    (TPrim2 (Lte, (TNum (4L, 2)), (TNum (2L, 3)), 1))

let test_tag_let () = 
  check tag_expr "same tag_expr"
    (tag (Let ("x", Num 4L, Prim2 (Add, Id "x", Num 2L))))
    (TLet ("x", (TNum (4L, 2)), TPrim2 (Add, (TId ("x", 4)), (TNum (2L, 5)), 3), 1))

let test_tag_if () = 
  check tag_expr "same tag_expr"
    (tag (If (Bool true, Num 4L, Prim2 (Add, Id "x", Num 2L))))
    (TIf 
      ((TBool (true, 2)), 
        (TNum (4L, 3)), 
        (TPrim2 (Add, (TId ("x", 5)), (TNum (2L, 6)), 4)), 
      1))

let test_tag_compound () = 
  check tag_expr "same tag_expr"
    (tag (Let 
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
    (compile_expr (TNum (1L, 1)) empty_slot_env 1L)
    ([IMov (Reg RAX, Const 2L)])

let test_compile_bool () = 
  check instruction_list "same instruction_list"
    (compile_expr (TBool (true, 1)) empty_slot_env 1L)
    ([IMov (Reg RAX, Const 3L)])

let test_compile_add1 () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim1 (Add1, (TNum (1L, 2)), 1)) empty_slot_env 1L)
    ([IMov (Reg RAX, Const 2L); IAdd (Reg RAX, Const 2L)])

let test_compile_sub1 () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim1 (Sub1, (TNum (1L, 2)), 1)) empty_slot_env 1L)
    ([IMov (Reg RAX, Const 2L); ISub (Reg RAX, Const 2L)])

let test_compile_not () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim1 (Not, (TBool (false, 2)), 1)) empty_slot_env 1L)
    ([IMov (Reg RAX, Const 1L); INot (Reg RAX) ; IAdd (Reg RAX, Const 1L)])

let test_compile_add () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim2 (Add, (TNum (4L, 2)), (TNum (2L, 3)), 1)) empty_slot_env 1L)
    ([IMov (Reg RAX, Const 8L); 
      IMov (StackPtr (RSP, 1L), Reg RAX); 
      IMov (Reg RAX, Const 4L) ; 
      IMov (StackPtr (RSP, 2L), Reg RAX);
      IMov (Reg RAX, StackPtr (RSP, 1L));
      IAdd (Reg RAX, StackPtr (RSP, 2L));
     ])

let test_compile_and () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim2 (And, (TBool (true, 2)), (TBool (true, 3)), 1)) empty_slot_env 1L)
    ([IMov (Reg RAX, Const 3L); 
      ICmp (Reg RAX, Const 1L);
      IJe ("skip_1");
      IMov (StackPtr (RSP, 1L), Reg RAX); 
      IMov (Reg RAX, Const 3L) ; 
      IMov (StackPtr (RSP, 2L), Reg RAX);
      IMov (Reg RAX, StackPtr (RSP, 1L));
      IAnd (Reg RAX, StackPtr (RSP, 2L));
      ILabel ("skip_1")
     ])

let test_compile_lte () = 
  check instruction_list "same instruction_list"
    (compile_expr (TPrim2 (Lte, (TNum (4L, 2)), (TNum (2L, 3)), 1)) empty_slot_env 1L)
    ([IMov (Reg RAX, Const 3L); 
      IMov (StackPtr (RSP, 1L), Reg RAX); 
      IMov (Reg RAX, Const 3L) ; 
      IMov (StackPtr (RSP, 2L), Reg RAX);
      IMov (Reg RAX, StackPtr (RSP, 1L));
      ICmp (Reg RAX, StackPtr (RSP, 2L));
      IJg ("if_else_1");
      IMov (Reg RAX, Const 3L);
      IJmp ("done_1");
      ILabel ("if_else_1");
      IMov (Reg RAX, Const 1L);
      ILabel ("done_1")
     ])

let test_compile_let () = 
  check instruction_list "same instruction_list"
    (compile_expr (TLet ("x", (TNum (4L, 2)), TPrim2 (Add, (TId ("x", 4)), (TNum (2L, 5)), 3), 1)) empty_slot_env 1L)
    ([IMov (Reg RAX, Const 8L);
      IMov (StackPtr (RSP, 1L), Reg RAX);
      IMov (Reg RAX, StackPtr(RSP, 1L));
      IMov (StackPtr (RSP, 2L), Reg RAX); 
      IMov (Reg RAX, Const 4L) ; 
      IMov (StackPtr (RSP, 3L), Reg RAX);
      IMov (Reg RAX, StackPtr (RSP, 2L)); 
      IAdd (Reg RAX, StackPtr (RSP, 3L));
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
      empty_slot_env 1L
    )
    ([IMov (Reg RAX, Const 3L);
      ICmp (Reg RAX, Const 1L);
      IJe ("if_false_1");
      IMov (Reg RAX, Const 8L);
      IJmp ("done_1");
      ILabel ("if_false_1");
      IMov (Reg RAX, Const 8L); 
      IMov (StackPtr (RSP, 1L), Reg RAX); 
      IMov (Reg RAX, Const 4L) ; 
      IMov (StackPtr (RSP, 2L), Reg RAX);
      IMov (Reg RAX, StackPtr (RSP, 1L));
      IAdd (Reg RAX, StackPtr (RSP, 2L));
      ILabel ("done_1");
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
        1)) empty_slot_env 1L)
    ([IMov (Reg RAX, Const 3L);
      IMov (StackPtr(RSP, 1L), Reg RAX);
      IMov (Reg RAX, Const 20L);
      IMov (StackPtr(RSP, 2L), Reg RAX);
      IMov (Reg RAX, Const 40L);
      IMov (StackPtr(RSP, 3L), Reg RAX);
      IMov (Reg RAX, StackPtr (RSP, 1L));
      IMov (StackPtr(RSP, 4L), Reg RAX);
      IMov (Reg RAX, StackPtr (RSP, 3L));
      ICmp (Reg RAX, StackPtr (RSP, 4L));
      IJg ("if_false_7");
      IMov (Reg RAX, Const 3L);
      IJmp ("done_7");
      ILabel ("if_false_7");
      IMov (Reg RAX, Const 1L);
      ILabel ("done_7");
      ICmp (Reg RAX, Const 1L);
      IJe ("skip_6");
      IMov (StackPtr(RSP, 3L), Reg RAX);
      IMov (Reg RAX, StackPtr (RSP, 1L));
      IMov (StackPtr (RSP, 4L), Reg RAX);
      IMov (Reg RAX, StackPtr (RSP, 3L));
      IAnd (Reg RAX, StackPtr (RSP, 4L));
      ILabel ("skip_6");
      ICmp (Reg RAX, Const 1L);
      IJe ("if_false_5");
      IMov (Reg RAX, Const 200L);
      IJmp ("done_5");
      ILabel ("if_false_5");
      IMov (Reg RAX, Const 3L);
      ILabel ("done_5");
     ])

(* OCaml tests: extend with your own tests *)
let ocaml_tests = [
  "parse", [
    test_case "A number" `Quick test_parse_int ;
    test_case "A variable" `Quick test_parse_var ;
    test_case "A compound expression" `Quick test_parse_compound ;
    test_case "An invalid s-expression" `Quick test_parse_error
  ] ;
  "interp", [
    test_case "A number" `Quick test_interp_num ;
    test_case "A variable" `Quick test_interp_var ;
    test_case "A compound expression" `Quick test_interp_compound
  ] ;
  "constructor", [
    test_case "A stack pointer constructor" `Quick test_constructor_rsp_pointer ;
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
    test_case "Tag a compound expression" `Quick test_tag_compound;
  ];
  "compile", [
    test_case "compile a num" `Quick test_compile_num;
    test_case "compile a bool" `Quick test_compile_bool;
    test_case "compile a add1" `Quick test_compile_add1;
    test_case "compile a sub1" `Quick test_compile_sub1;
    test_case "compile a not" `Quick test_compile_not;
    test_case "compile a +" `Quick test_compile_add;
    test_case "compile a &&" `Quick test_compile_and;
    test_case "compile a let" `Quick test_compile_let;
    test_case "compile a if" `Quick test_compile_if;
    test_case "compile a compound" `Quick test_compile_compound;
  ]
]     

(* Entry point of tester *)
let () =
  (* BBC tests: don't change the following, simply add .bbc files in the bbctests/ directory *)
  let bbc_tests = 
    let compile_flags = Option.value (Sys.getenv_opt "CFLAGS") ~default:"-g" in
    let compiler : string -> out_channel -> unit = 
      fun s o -> fprintf o "%s" (compile (parse_exp (sexp_from_string s))) in
    let interpreter : string -> string = 
      fun s -> string_of_val (interp (parse_exp (sexp_from_string s)) empty_env) in
    tests_from_dir ~compile_flags ~compiler ~interpreter ~runtime:"rt/sys.c" "bbctests" in
  run "Tests entrega 1" (ocaml_tests @ bbc_tests)
