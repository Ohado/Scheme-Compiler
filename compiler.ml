#use "code-gen.ml";;

let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;

let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s));;

(* a mapping from free-variable names of primitive library procedures
  to their corresponding assembly code labels *)
let primitive_names_to_labels = 
  ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "binsub", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";

   "boolean?", "is_boolean"; "car", "car_prim"; "cdr", "cdr_prim"; "cons", "cons_prim"; "set-car!",
   "set_car_prim"; "set-cdr!", "set_cdr_prim"; "apply", "apply_prim"
(* you can add yours here *)];;

let make_prologue consts_tbl fvars_tbl =
  let get_const_address const = Code_Gen.get_const_idx const consts_tbl in
  (* This function takes a single constant and returns a string representing its absolute address. *)
  let get_fvar_address fvar = Code_Gen.get_fvar_idx fvar fvars_tbl in
  (* This function takes a single free-variable name and returns a string representing its absolute address. *)
  let make_primitive_closure (prim, label) =
  (* a mapping from free-variable names of primitive library procedures to their corresponding assembly code labels *)
"    MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ label  ^ ")
    mov qword FVAR("^string_of_int(get_fvar_address prim)^"), rax"
    in
  let make_constant (c, (a, s)) = s in
  
"
;;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include \"compiler.s\"

section .bss
malloc_pointer:
    resq 1

section .data
const_tbl:
" ^ (String.concat "\n" (List.map make_constant consts_tbl)) ^ "

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS " ^ get_const_address Void ^ "
%define SOB_NIL_ADDRESS " ^ get_const_address (Sexpr Nil) ^ "
%define SOB_FALSE_ADDRESS " ^ get_const_address (Sexpr (Bool true)) ^ "
%define SOB_TRUE_ADDRESS " ^ get_const_address (Sexpr (Bool false)) ^ "

fvar_tbl:
" ^ (String.concat "\n" (List.map (fun _ -> "dq T_UNDEFINED") fvars_tbl)) ^ "

section .text
main:
    ;; set up the heap
    mov rdi, GB(4)
    call malloc
    mov [malloc_pointer], rax

    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 5578) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push 0
    push qword SOB_NIL_ADDRESS
    push qword T_UNDEFINED
    push rsp
    mov rbp, rsp

    call code_fragment
    add rsp, 4*8
    ret


code_fragment:
    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we emulate the missing (define ...) expressions
    ;; for all the primitive procedures.
" ^ (String.concat "\n" (List.map make_primitive_closure primitive_names_to_labels)) ^ "

actual_code:
";;

let epilogue = ";; That's all, folks!";;
let prim_start =
"ret \n\n;***************************************\n ;; ********* Prim Functions: ********** \n;***************************************\n\n"

exception X_missing_input_file;;

try
  let infile = Sys.argv.(1) in
  let code =  (file_to_string "stdlib.scm") ^ (file_to_string infile) in
  let asts = string_to_asts code in
  let consts_tbl = Code_Gen.make_consts_tbl asts in
  (* NOTE: I "contaminate" the asts here with the names of all the primitive functions *)
  let fvars_tbl = Code_Gen.make_fvars_tbl (asts @ (map (fun (a, b)-> (Code_Gen.analyze_string a)) primitive_names_to_labels)) in
  let generate = Code_Gen.generate consts_tbl fvars_tbl in
  let code_fragment = (String.concat "\n\n"
                        (List.map
                           (fun ast -> (generate ast) ^ "\n;;before_print:\n    call write_sob_if_not_void \n")
                           asts)) ^ prim_start in
  let provided_primitives = file_to_string "prims.s" in
                   
  print_string ((make_prologue consts_tbl fvars_tbl)  ^
                  code_fragment ^
                    provided_primitives ^ "\n" ^ epilogue)

with Invalid_argument(x) -> raise X_missing_input_file;;
