open Dev.Ast
open Dev.Asm
open Dev.Parse
open Dev.Compile
open Dev.Interp
open Alcotest
open Dev.Regsandstack

(* Testing arithmetic expression using the print function defined in Interp 
   and the default equality for comparison *)
let exp : expr testable =
  testable (fun oc e -> Format.fprintf oc "%s" (string_of_expr e)) (=)

let prog : prog testable =
  testable (fun oc e -> Format.fprintf oc "%s" (string_of_prog e)) (=)

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
    check exp "same tuple" (parse_exp (`List [`Atom "tup"; `Atom "true" ; `Atom "1"])) (*(Tuple [(Bool true);(Num 1L)] )*)
  (Let ("arg2", (Bool true), Let ("arg1", (Num 1L), Tuple ([Id "arg2"; Id "arg1"]))))

let test_parse_get () =
  check exp "get applies" (parse_exp (`List [`Atom "get" ; `Atom "1";`Atom "2"]))
                          (Let ("arg1", Num 1L, Let ("arg2", Num 2L, Prim2 (Get, Id "arg1", Id "arg2"))))

let test_parse_set () =
  check exp "set applies" (parse_exp (`List [`Atom "set" ; `Atom "true";`Atom "37";`Atom "3"]))
                          (Let ("arg1", Bool true, Let ("arg2", Num 37L, Let ("arg3", Num 3L, Set (Id "arg1", Id "arg2", Id "arg3")))))

let test_parse_record () =
  check prog "same record" (parse_prog (`List [`List [`Atom "record" ; `Atom "point2d" ; `Atom "x" ; `Atom "y"] ; `Atom "1"]))
                          (([DefFun ("point2d", ["x"; "y"], Tuple ([Id "x" ; Id "y"])) ;
                            DefFun ("point2d_x", ["t"], (Let ("arg1", Id "t", Let ("arg2", Num 0L, Prim2 (Get, Id "arg1", Id "arg2"))))); 
                            DefFun ("point2d_y", ["t"], (Let ("arg1", Id "t", Let ("arg2", Num 1L, Prim2 (Get, Id "arg1", Id "arg2")))))], Num 1L))


let test_tag_tup () =
  check tag_expr_t "same tag expr" (tag_expr (Tuple ([Id "arg1"; Id "arg2"])))
                            (TTuple ([TId ("arg1", 2) ; TId ("arg2", 3)], 1))

let test_tag_get () =
  check tag_expr_t "same tag expr" (tag_expr (Prim2 (Get, Id "x", Num 0L)))
                            (TPrim2 (Get, (TId ("x", 2)), (TNum (0L, 3)), 1))

let test_tag_set () =
  check tag_expr_t "same get" (tag_expr (Set (Id "x", Num 0L, Num 5L)))
                       (TSet (TId ("x", 2), TNum (0L, 3), TNum (5L, 4), 1))


let test_compile_tuple () =
  check instruction_list "same tuple" (compile_expr (tag_expr (Tuple ([Id "arg1"; Id "arg2"]))) [("arg2", -2L) ; ("arg1", -1L)] (Int64.sub 0L 3L) empty_comp_fenv 0 0)
                         ([
                          iPush r11 ;
                          iMov_arg_arg r11 r15 ;
                          iMov_arg_const (Ptr (R11, 0L)) (8L(*Int64.of_int (4 * (List.length attrs))*)) ;
                          iAdd_arg_const r15 (24L(*Int64.of_int (8 * (List.length attrs + 1))*))
                        ] @
                        (*(compile_lexpr lst 1) (* <=> *)*)
                        [
                          iMov_arg_to_RAX (Ptr(RBP, -1L))
                        ] @
                        (*(compile_expr hd slot_env next_slot fenv tag_fun total_params)*) 
                        [iMov_arg_arg (Ptr (R11, (1L(*Int64.of_int param_pos*)))) rax] @
                        [
                          iMov_arg_to_RAX (Ptr(RBP, -2L))  
                        ]
                        (*(compile_expr hd slot_env next_slot fenv tag_fun total_params)*) @
                        [iMov_arg_arg (Ptr (R11, (2L(*Int64.of_int param_pos*)))) rax]
                        (*(compile_lexpr tl (param_pos + 1))*) @
                        [
                          iMov_arg_to_RAX r11 ;
                          iAdd_arg_const rax 1L ;
                          iPop r11
                        ] @
                        [
                          iAdd_arg_const r15 7L ;
                          iPush r11 ;
                          iMov_arg_const r11 (Int64.mul Int64.minus_one 8L) ;
                          iAnd_arg_arg r15 r11 ; 
                          iPop r11
                        ]
                        )

let test_compile_get () =
  check instruction_list "same get" (compile_expr (tag_expr (Prim2 (Get, Id "x", Id "y"))) [("x", -1L) ; ("y", -2L)] (Int64.sub 0L 3L) empty_comp_fenv 0 0)
                       (
                        let r10_ptr = Ptr(R10, 0L) in
                        
                        [ iMov_arg_to_RAX (Ptr(RBP, -1L)) ] @
                        [ iMov_arg_arg (Ptr(RBP, -3L)) rax] @
                        [ iMov_arg_to_RAX (Ptr(RBP, -2L)) ] @
                        [ iMov_arg_arg (Ptr(RBP, -4L)) rax ] @
                        [ iMov_arg_to_RAX (Ptr(RBP, -3L))] @
                        [
                          iPush r10 ;
                          iPush r11 ;
                          iMov_arg_arg r10 rax
                          
                        ] @
                        (check_rax_is_tuple_instr (Int64.sub (Int64.sub 0L 4L) 1L)) @
                        [
                          iSub_arg_const r10 1L ;
                          iMov_arg_arg r11 (Ptr(RBP, -4L)) ;
                          iMov_arg_to_RAX (Ptr(RBP, -4L))
                        ] @
                        (check_rax_is_int_instr (Int64.sub 0L 4L)) @
                        [iMov_arg_arg r11 (Ptr(RBP, -4L))] @
                        [
                          iCmp_arg_const r11 0L ;
                          IJl "index_too_low" ;
                          iCmp_arg_arg r11 r10_ptr ;
                          IJge "index_too_high" ;
                          iSar r11 2L ;
                          iAdd_arg_const r11 1L ;
                          iSal r11 3L ;
                          iAdd_arg_arg r10 r11 ;
                          iMov_arg_to_RAX r10_ptr ;
                          iPop r11 ;
                          iPop r10
                        ] 
                       )
  
let test_compile_set () =
  check instruction_list "same set" (compile_expr (tag_expr (Set (Id "t", Id "p", Id "x"))) [("x", -3L) ; ("p", -2L) ; ("t", -1L)] (Int64.sub 0L 4L) empty_comp_fenv 0 0)
                       (
                        [ iMov_arg_to_RAX (Ptr(RBP, -1L)) ] @
                        (check_rax_is_tuple_instr (-4L)) @
                        [ iMov_arg_to_RAX (Ptr(RBP, -2L)) ;
                          iMov_arg_arg (rbp_pointer (-5L)) rax ; 
                          iMov_arg_arg rax (rbp_pointer (-5L))
                        ] @
                        (check_rax_is_int_instr (-5L)) @
                        [ iMov_arg_to_RAX (Ptr(RBP, -3L)) ;
                          iMov_arg_arg (rbp_pointer (Int64.sub (-5L) 1L)) rax ;
                          iPush r10 ;
                          iPush r11 ;
                          iMov_arg_arg r10 (Ptr(RBP, -4L)) ;
                          iSub_arg_const r10 1L ;
                          iMov_arg_arg r11 (rbp_pointer (-5L)) ;
                          iCmp_arg_const r11 0L ;
                          IJl "index_too_low" ;
                          iCmp_arg_arg r11 (Ptr(R10, 0L)) ;
                          IJge "index_too_high" ;
                          iSar r11 2L ;
                          iAdd_arg_const r11 1L ;
                          iSal r11 3L ;
                          iAdd_arg_arg r10 r11 ;
                          iMov_arg_arg r11 (rbp_pointer (Int64.sub (-5L) 1L)) ;
                          iMov_arg_arg (Ptr(R10, 0L)) r11 ;
                          iPop r11 ;
                          iPop r10 ;
                          iMov_arg_to_RAX (Ptr(RBP, -4L))(*rbp_ptr*)
                        ]
                       )
      
(*let test_compile_set () =
  check arg "same set" (compile_expr (tag_prog (Set (Id "x", 0, Num 5L)) empty_slot_env (Int64.sub 0L 2L) empty_comp_fenv 0 0)
                       ([fetch_to_stack -1 ; check_index_range ; move_to_RAX (Num 20L) ; set_RAX_on_heap 2])*)


                      
