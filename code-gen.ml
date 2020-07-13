#use "semantic-analyser.ml";;
exception X_not_found_in_fvar;;
exception X_not_found_in_def;;
exception X_not_found_in_const;;
open List;;

let sa s = Semantics.run_semantics (tp s);;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
  val get_const_idx : constant -> (constant * (int * string)) list -> int
  val get_fvar_idx : string -> (string * int) list -> int
  val analyze_string: string -> expr'
end;;

module Code_Gen : CODE_GEN = struct

(* end;; *)

(* This function turns a string into an expr' *)
let analyze_string s = Semantics.run_semantics (tp s);;

(* ****************************************** *)
let const_idx = ref(0)

let get_const_size c =
  match c with
    | Void -> 1
    | (Sexpr (Bool _)) -> 2
    | (Sexpr (Nil)) -> 1
    | (Sexpr (Number _ )) -> 9
    | (Sexpr (Char _)) -> 2
    | (Sexpr (Symbol _)) -> 9
    | (Sexpr (String s)) -> 9 + (String.length s)
    | (Sexpr (Vector slist)) -> 9 + ((length slist) * 8)
    | (Sexpr (Pair (_, _))) -> 17

let generate_const_idx c =
  let x = !const_idx in
    const_idx := !const_idx + (get_const_size c);
    x;;

let rec add_to_base_const_tbl ast tbl =
  match ast with
    | Const' c -> (match c with
      | (Sexpr (Symbol s)) -> tbl @ [Sexpr (String s) ; c]
      | (Sexpr (Pair (a, b))) -> fold_right add_to_base_const_tbl [Const'(Sexpr a);Const'(Sexpr b)] tbl @ [c]
      | (Sexpr (Vector slist)) -> let slist = map (fun a-> Const'(Sexpr a)) slist in
                                    fold_right add_to_base_const_tbl slist tbl @ [c]
      | _ -> tbl @ [c]  )
    | BoxSet'(v, e) -> add_to_base_const_tbl e tbl
    | If' (e1, e2, e3) -> fold_right add_to_base_const_tbl [e1; e2; e3] tbl
    | Seq' slist -> fold_right add_to_base_const_tbl slist tbl
    | Set' (e1, e2) -> fold_right add_to_base_const_tbl [ e1; e2] tbl
    | Def' (e1, e2) -> add_to_base_const_tbl e2 tbl
    | Or' slist -> fold_right add_to_base_const_tbl slist tbl
    | LambdaSimple' (slist, e) -> let slist = map (fun a-> Const'(Sexpr (String a))) slist in
                                  fold_right add_to_base_const_tbl (slist @ [e]) tbl
    | LambdaOpt' (slist, opt, e) -> let slist = map (fun a-> Const'(Sexpr (String a))) (opt::slist) in
                                    fold_right add_to_base_const_tbl (slist @ [e]) tbl
    | Applic' (op, elist) -> fold_right add_to_base_const_tbl ([op] @ elist) tbl
    | ApplicTP' (op, elist) -> fold_right add_to_base_const_tbl ([op] @ elist) tbl
    | _ -> tbl

let make_base_const_list asts = fold_right add_to_base_const_tbl (rev asts) [Void; Sexpr(Nil); Sexpr(Bool false); Sexpr(Bool true)];;

let rec list_const_remove_dup tbl =
  if (List.length tbl) = 0 then tbl else
    let c1 = (List.hd tbl) in
      let (_, parted) = partition (fun c2 -> (expr_eq (Const c1) (Const c2))) tbl in
        [c1] @ (list_const_remove_dup parted);;

let get_const_idx c1 tbl = try
  let const = List.find (fun (c2, (_, _)) -> expr_eq (Const c2) (Const c1)) tbl in
    let (_, (offset, _)) = const in offset
  with Not_found -> raise X_not_found_in_const


let rec make_vector_cmd tbl vec str =
  if (length vec = 0) then str^" ;" else
  let hd = (hd vec) in
    if (length vec = 1) then
      str ^ "const_tbl+"^string_of_int (get_const_idx (Sexpr hd) tbl)^" ;" else
        let new_str = str ^ "const_tbl+"^string_of_int (get_const_idx (Sexpr hd) tbl)^", " in
          make_vector_cmd tbl (tl vec) new_str

(* let replace_special_char c =
  let cnum = int_of_char c in
    if cnum < 33 then "',"^cnum^", '"
    else c *)

let add_to_const_tbl tbl c =
  let idx = generate_const_idx c in
  let sidx = string_of_int idx in
  let remove_special s =
    let s = String.concat ("\", 10, \"") (String.split_on_char '\n' s) in
    String.concat ("\", 13, \"") (String.split_on_char '\r' s) in
  let switch_special c =
    let ascii = (int_of_char c) in
      if (ascii < 32) then (string_of_int ascii) else
        "\""^(String.make 1 c)^"\"" in
    (* if (c = '\n') then "10" else
    if (c = '\r') then "13" else
    if (c = '\t') then "9" else *)
  match c with
    | Void -> tbl @ [(c, (idx, "MAKE_VOID ;"^sidx))]
    | (Sexpr (Bool false)) -> tbl @ [(c, (idx, "MAKE_BOOL(0) ;"^sidx))]
    | (Sexpr (Bool true)) -> tbl @ [(c, (idx, "MAKE_BOOL(1) ;"^sidx))]
    | (Sexpr (Nil)) -> tbl @ [(c, (idx, "MAKE_NIL ;"^sidx))]
    | (Sexpr (Number (Int i) )) -> tbl @ [(c, (idx, "MAKE_LITERAL_INT("^(string_of_int i)^") ;"^sidx))]
    | (Sexpr (Number (Float f) )) -> tbl @ [(c, (idx, Printf.sprintf "MAKE_LITERAL_FLOAT(%f) ;" f^sidx))]
    | (Sexpr (Char ch)) -> tbl @ [(c, (idx, "MAKE_LITERAL_CHAR("^switch_special ch^") ;"^sidx))]
    | (Sexpr (String s)) -> tbl @ [(c, (idx, "MAKE_NEW_LITERAL_STRING \""^remove_special s^"\" ;"^sidx))]
    | (Sexpr (Symbol s)) -> tbl @ [(c, (idx, "MAKE_LITERAL_SYMBOL(const_tbl+"^string_of_int (get_const_idx (Sexpr (String s)) tbl)^") ;"^sidx))]
    | (Sexpr (Pair (a, b))) -> tbl @ [(c, (idx, "MAKE_LITERAL_PAIR(const_tbl+"^string_of_int (get_const_idx (Sexpr a) tbl)^", const_tbl+"^string_of_int (get_const_idx (Sexpr b) tbl)^") ;"^sidx))]
    | (Sexpr (Vector elist)) -> tbl @ [(c, (idx, (make_vector_cmd tbl elist "MAKE_LITERAL_VECTOR "^sidx)))]

  let make_consts_tbl asts =
  (* [(Sexpr(Number(Int(5)), (5, "ggg"))] *)
    let dup_base_tbl = make_base_const_list asts in
      let base_tbl = list_const_remove_dup dup_base_tbl in
        fold_left add_to_const_tbl [] base_tbl

(* ********************************************************************** *)

let fvar_idx = ref(0)

let generate_nat_idx idx =
  let x = !idx in
    idx := !idx + 1;
    x;;

let rec add_to_base_fvar_tbl ast tbl =
  match ast with
    | Var'(VarFree v) -> tbl @ [v]
    | Box'(VarFree v) -> tbl @ [v]
    | BoxGet'(VarFree v) -> tbl @ [v]
    | BoxSet'((VarFree v), e) -> add_to_base_fvar_tbl e (tbl @ [v])
    | BoxSet'(v, e) -> add_to_base_fvar_tbl e tbl
    | If' (e1, e2, e3) -> fold_right add_to_base_fvar_tbl [e1; e2; e3] tbl
    | Seq' slist -> fold_right add_to_base_fvar_tbl slist tbl
    | Set' (e1, e2) -> fold_right add_to_base_fvar_tbl [ e1; e2] tbl
    | Def' (e1, e2) -> fold_right add_to_base_fvar_tbl [ e1; e2] tbl
    | Or' slist -> fold_right add_to_base_fvar_tbl slist tbl
    | LambdaSimple' (slist, e) -> add_to_base_fvar_tbl e tbl
    | LambdaOpt' (slist, opt, e) -> add_to_base_fvar_tbl e tbl
    | Applic' (op, elist) -> fold_right add_to_base_fvar_tbl ([op] @ elist) tbl
    | ApplicTP' (op, elist) -> fold_right add_to_base_fvar_tbl ([op] @ elist) tbl
    | _ -> tbl

let make_base_fvar_list asts = fold_right add_to_base_fvar_tbl asts [];;

let rec list_remove_dup tbl =
  if (List.length tbl) = 0 then tbl else
    let e1 = (List.hd tbl) in
      let (_, parted) = partition (fun e2 -> (e1 = e2)) tbl in
        [e1] @ (list_remove_dup parted);;

let get_fvar_idx f1 tbl = try
  let fvar = List.find (fun (f2, _) -> (f2) = (f1)) tbl in
    let (_, offset) = fvar in offset
  with Not_found -> raise X_not_found_in_fvar

let gets_fvar_idx f1 tbl = try string_of_int (get_fvar_idx f1 tbl)
  with X_not_found_in_fvar -> raise X_not_found_in_def

let add_to_fvar_tbl var = (var, generate_nat_idx fvar_idx)

let make_fvars_tbl asts =
  let dup_fbase_tbl = make_base_fvar_list asts in
    let fbase_tbl = list_remove_dup dup_fbase_tbl in
      map add_to_fvar_tbl fbase_tbl

(* ****************************************************************************** *)

let if_idx = ref(1)
let or_idx = ref(1)
let lam_idx = ref(1)
let app_idx = ref(1)

let word_size = 8

let inc env_s = (string_of_int ((int_of_string env_s) + 1))
let repeat_str s n = String.concat "" (Array.to_list (Array.make n s))

let generate_str_idx i = string_of_int (generate_nat_idx i)

  let rec gen_e consts fvars lam_hist e =
    let (depth, parent_params_num) = lam_hist in
  "\n" ^
    (match e with
      | Const'(c) -> gen_const consts c
      | Var'(v) -> gen_var consts fvars lam_hist v
      | Box' (v) -> gen_box consts fvars lam_hist v
      | BoxGet' (v) -> gen_box_get consts fvars lam_hist v
      | BoxSet' (v, e) -> gen_box_set consts fvars lam_hist v e
      | If' (e1, e2, e3) -> (gen_if consts fvars lam_hist e1 e2 e3)
      | Seq' (elist) ->
      "; Sequence starts:" ^ (gen_seq consts fvars lam_hist elist) ^ "\n; :Sequence ends"
      | Set' (e1, e2) -> gen_set consts fvars lam_hist e1 e2
      | Def' (e1, e2)-> gen_def consts fvars lam_hist e1 e2
      | Or' (elist) -> (gen_or consts fvars lam_hist elist)
      | LambdaSimple' (slist, body) -> gen_lamSim consts fvars (depth + 1) parent_params_num slist body
      | LambdaOpt' (slist, opt_s, body) -> gen_lamOpt consts fvars (depth + 1) parent_params_num slist body
      | Applic' (op, elist) -> gen_applic consts fvars lam_hist op elist
      (* TEMPORARILY TREATED AS A NORMAL APPLIC: *)
      | ApplicTP' (op, elist) -> "; this is an ApplicTP! \n" ^ gen_applic_tp consts fvars lam_hist op elist
  )

and gen_applic_tp consts fvars lam_hist op elist =
  let gen = gen_e consts fvars lam_hist in
  let idx = generate_str_idx app_idx in
  let argcount = string_of_int (length elist) in
  let new_frame_size = (length elist) + 4 in
  let gen_arg arg s = s ^ gen arg ^ "\n push rax" in
" ApplicTP"^idx^":
mov r9, 8875
push r9   ; push the magic param first
" ^ (fold_right gen_arg elist "") ^ "
mov r9, "^argcount^"
push r9   ; This is the number of the parameters
"^gen op^"    ; rax has the operator. We assume it's a lambda.
add rax, TYPE_SIZE
push qword[rax] ; = push rax + TYPE_SIZE; pushing the env
push qword[ rbp + 8 * 1 ]  ; push the OLD return address. We won't come back.
mov rbx, [rbp + 8 * 0]  ; rbx = old rbp. The lambda getting it will never know we've been here
; SHIFT_FRAME "^string_of_int new_frame_size^"  ; shift frame uses current rbp & rcx

  shifty"^idx^":
	mov rcx, [rbp + WORD_SIZE * 3]
	add rcx, 5
  mov rsi, rcx
%assign i 1
%rep "^string_of_int new_frame_size^"
	dec rcx
	mov r8, [rbp-WORD_SIZE*i]
  mov r9, [rbp+WORD_SIZE*rcx]
	mov [rbp+WORD_SIZE*rcx], r8
%assign i i+1
%endrep

mov rbp, rbx
shl rsi, 3   ; this is the actual size of the old env. The amount we need to fix
add rsp, rsi  ; clear the new frame and fix the stack

add rax, WORD_SIZE
jmp [rax] ; = call rax + TYPE_SIZE + WORD_SIZE, jump to the body and never come back. Goodbye!
; :::end of ApplicTP"^idx

and gen_lamOpt consts fvars extended_environment_depth parent_parameters_number current_params body =
  let gen_e = gen_e consts fvars (extended_environment_depth, ((length current_params) + 1)) in
  let idx = generate_str_idx lam_idx in
  (* creation or extension of environment *)
  let environment_creation =
  " ; creation or extension of environment\n"^
  (if (extended_environment_depth = 0)
    then
      ("mov rbx, SOB_NIL_ADDRESS  ; no address required, we are in the global environment\n")
    else
      (if (extended_environment_depth = 1)
        then
          ("MALLOC rbx, 8  ; rbx = address of new env\n"^
            (if(parent_parameters_number = 0)
              then
                ("mov qword [rbx], SOB_NIL_ADDRESS   ; empty vector: no arguments on stack\n")
              else
                ("MALLOC rdx, "^string_of_int (8 * parent_parameters_number)^" ; rdx = address of new vector\n"^
                  "mov [rbx], rdx"^
                  (params_to_vector parent_parameters_number 0))
          ))
        else
        ("MALLOC rbx, "^(string_of_int (8*extended_environment_depth))^" ; rbx = address of new env          \n"^
          "mov rcx, rbx          \n"^
          "add rcx, 8  ; rcx will move through the new env          \n"^
          "mov rdi, qword[rbp + 8*2] ; rdi = address of old env          \n"^
          (copy_old_env_to_new_env (extended_environment_depth-1) 0)^
            (if(parent_parameters_number = 0)
                then
                  ("mov qword [rbx], SOB_NIL_ADDRESS   ; empty vector: no arguments on stack\n")
                else
                  ("MALLOC rdx, "^string_of_int (8 * parent_parameters_number)^" ; rdx = address of new vector    \n"^
                    "mov [rbx], rdx   \n"^
                    (params_to_vector parent_parameters_number 0))))
        ))  in
  let closure_creation =
  "MAKE_CLOSURE(rax, rbx, lambda_body_"^idx^")\n" in
  let body_creation =
  "jmp lambda_end_body_"^idx^"
   lambda_body_"^idx^":
    push rbp
    mov rbp, rsp

    mov rcx, qword[rbp + 8*3]
    mov rbx, "^string_of_int (length current_params)^"
    cmp rbx, rcx  ; how many optional arguments are practically in stack?
    je no_optionals_parameters"^idx^"

    ; turn the optional parameters to list
    mov rcx, qword[rbp + 8*3]
    sub rcx, "^string_of_int (length current_params)^"  ; rcx = number of optional parameters
    dec rcx
    mov rdx, qword[rbp + 8*(4+"^string_of_int (length current_params)^"+rcx)]    ; rdx = last optional parameter
    mov rbx, rdx    ; rbx = our future list
    MAKE_PAIR(rax, rbx, const_tbl+1)  ; make improper list: (rbx, nil)
    mov rbx, rax
  params_to_list_loop_"^idx^":
    dec rcx
    cmp rcx, -1
    je end_params_to_list_loop_"^idx^"
    mov rdx, qword[rbp + 8*(4+"^string_of_int (length current_params)^"+rcx)]    ; rdx = an optional parameter
    MAKE_PAIR(rax, rdx, rbx)  ; make pair: (rdx, rbx)
    mov rbx, rax
    jmp params_to_list_loop_"^idx^"
  end_params_to_list_loop_"^idx^":
    mov qword[rbp + 8*(4+"^string_of_int (length current_params)^")], rax   ; replace the first optional parameter with the optional list
    jmp body_cont"^idx^"

  no_optionals_parameters"^idx^":
    mov rcx, const_tbl+1
    mov qword[rbp + 8*(4+"^(string_of_int (length current_params))^")], rcx
    jmp body_cont"^idx^"

  body_cont"^idx^":
    "^(gen_e body)^"
    leave
    ret
   lambda_end_body_"^idx^":\n"  in

  "LambdaOpt"^idx^":\n"^environment_creation^closure_creation^body_creation^";:::end of LambdaOpt"^idx^":"


and gen_box_set consts fvars lam_hist v e =
  let gen_e = gen_e consts fvars lam_hist in
  let gen_var = gen_var consts fvars lam_hist in
  "; Setting a boxed variable:
  "^gen_e e^"
  push rax  ; the stack has now the value we need
  "^gen_var v^"   ; rax = v's box
  pop qword[rax]   ; Now v's box points the new value
  mov rax, sob_void
  "

and gen_box_get consts fvars lam_hist v =
  "; Getting a boxed variable:
  "^gen_var consts fvars lam_hist v^"
  mov rax, qword[rax]   ; the value is one pointer inside the box
  "

and gen_box consts fvars lam_hist v =
  "; Boxing is needed. We need to replace the var with a pointer to it.
  MALLOC rbx, 8   ; rbx will hold the pointer. Now we'll get the var to rax:
  "^gen_var consts fvars lam_hist v^"
  mov qword[rbx], rax ; now rbx is a pointer to the var!
  mov rax, rbx\n"

and gen_set consts fvars lam_hist var e =
  let gen_e = gen_e consts fvars lam_hist in
  ";; Set!
    "^ gen_e e ^"; Now let's set var to rax:\n"^
  (match var with
    | Var' (VarParam (name, minor)) ->
" mov qword [rbp + 8 * (4 + "^string_of_int minor^")], rax    ; setting param "^name^"
  mov rax, sob_void"
    | Var' (VarBound (name, major, minor)) ->
" mov rbx, qword [rbp + 8 * 2]  ; current environment
  mov rbx, qword [rbx + 8 * "^string_of_int major^"]  ; a vector
  mov qword [rbx + 8 * "^string_of_int minor^"], rax  ; a value from rax to bound "^name^"
  mov rax, sob_void"
    | Var' (VarFree name) -> let idx = gets_fvar_idx name fvars in
        gen_e e ^ "
  mov qword FVAR("^idx^"), rax    ; defining "^name^"
  mov rax, sob_void"
    | _ -> "who's the fool who's defining a non-var?"
)

and gen_applic consts fvars lam_hist op elist =
  let gen = gen_e consts fvars lam_hist in
  let idx = generate_str_idx app_idx in
  let argcount = string_of_int (length elist) in
  let gen_arg arg s = s ^ gen arg ^ "\n push rax" in
" Applic"^idx^":
mov r9, 8875
push r9   ; push the magic param first"
 ^ (fold_right gen_arg elist "") ^ "
mov r9, "^argcount^"
push r9   ; This is the number of the parameters
"^gen op^"    ; That was the operator. We assume it's a lambda.
add rax, TYPE_SIZE
push qword[rax] ; = push rax + TYPE_SIZE;  pushing the env
add rax, WORD_SIZE
call [rax] ; = call rax + TYPE_SIZE + WORD_SIZE, call the body

add rsp, WORD_SIZE  ; pop the env
pop rbx   ; rbx has argcount now
add rbx, 1   ; rbx = argcount + magic
shl rbx, 3   ; rbx = rbx * 8
add rsp, rbx  ; pop all args + magic, back to normal
; :::end of Applic"^idx

(* Generation of lambda: *)
and params_to_vector parent_parameters_number i =
  if(i < parent_parameters_number)
  then "
      mov rsi, qword[rbp + 8*(4+ "^string_of_int i^")]
      mov [rdx], rsi
      add rdx, 8
      "^(params_to_vector parent_parameters_number (i+1))
  else
    ""

and copy_old_env_to_new_env depth i =
  if (i <= depth)
  then
  "mov rsi, [rdi + "^(string_of_int (i*8))^"]
    mov [rcx], rsi
    add rcx, 8\n"
    ^(copy_old_env_to_new_env depth (i+1))
  else
  ("")

and gen_lamSim consts fvars extended_environment_depth parent_parameters_number current_params body =
  let gen_e = gen_e consts fvars (extended_environment_depth, (length current_params)) in
  let idx = generate_str_idx lam_idx in
  (* creation or extension of environment *)
  let environment_creation =
  " ; creation or extension of environment\n"^
  (if (extended_environment_depth = 0)
    then
      ("mov rbx, SOB_NIL_ADDRESS  ; no address required, we are in the global environment\n")
    else
      (if (extended_environment_depth = 1)
        then
          ("MALLOC rbx, 8  ; rbx = address of new env\n"^
            (if(parent_parameters_number = 0)
              then
                ("mov qword [rbx], SOB_NIL_ADDRESS   ; empty vector: no arguments on stack\n")
              else
                ("MALLOC rdx, "^string_of_int (8 * parent_parameters_number)^" ; rdx = address of new vector\n"^
                  "mov [rbx], rdx"^
                  (params_to_vector parent_parameters_number 0))
          ))
        else
        ("MALLOC rbx, "^(string_of_int (8*extended_environment_depth))^" ; rbx = address of new env          \n"^
          "mov rcx, rbx          \n"^
          "add rcx, 8  ; rcx will move through the new env          \n"^
          "mov rdi, qword[rbp + 8*2] ; rdi = address of old env          \n"^
          (copy_old_env_to_new_env (extended_environment_depth-1) 0)^
            (if(parent_parameters_number = 0)
                then
                  ("mov qword [rbx], SOB_NIL_ADDRESS   ; empty vector: no arguments on stack\n")
                else
                  ("MALLOC rdx, "^string_of_int (8 * parent_parameters_number)^" ; rdx = address of new vector    \n"^
                    "mov [rbx], rdx   \n"^
                    (params_to_vector parent_parameters_number 0))))
        ))  in
  let closure_creation =
  "MAKE_CLOSURE(rax, rbx, lambda_body_"^idx^")\n" in
  let body_creation =
  "jmp lambda_end_body_"^idx^"
   lambda_body_"^idx^":
    push rbp
    mov rbp, rsp
    "^(gen_e body)^"
    aftecode"^idx^":
    leave
    afteleave"^idx^":
    ret
   lambda_end_body_"^idx^":\n"  in

  "Lambda"^idx^":\n"^environment_creation^closure_creation^body_creation^";:::end of Lambda"^idx^":"


and gen_def consts fvars lam_hist var e =
  match var with
    | Var' (VarFree name) -> (
      let gen_e = gen_e consts fvars lam_hist in
      let idx = gets_fvar_idx name fvars in
        gen_e e ^ "
  mov qword FVAR("^idx^"), rax    ; defining "^name^"
  mov rax, sob_void")
    | _ -> "who's the fool who's defining a non-freevar?"

and gen_var consts fvars lam_hist v =
  (* let gen_e = gen_e consts fvars in *)
  match v with
  | VarFree(n) -> let idx = string_of_int (get_fvar_idx n fvars) in
    "mov rax, FVAR("^idx^")   ; Get the freevar "^n
  | VarParam(name, min) ->
    " ;; Get_param "^name^":
    ;Param "^name^":
  mov r8, "^string_of_int min^"
  add r8, 4
  shl r8, 3
  add r8, rbp
  mov rax, qword [r8] ;; mov rax, qword [rbp + WORD_SIZE * (4 + "^string_of_int min^")]"
  | VarBound(name, major, minor) -> let maj, min = string_of_int major, string_of_int minor in
    " ;Get_bound "^name^":
  mov rax, qword [rbp + 8 * 2]  ; current environment
  mov rax, qword [rax + 8 * "^maj^"]  ; a vector
  mov rax, qword [rax + 8 * "^min^"]  ; a value
  "

and gen_or consts fvars lam_hist elist =
  let gen_e = gen_e consts fvars lam_hist in
  let idx = generate_str_idx or_idx in
  let lexit = "LexitOr" ^ idx in
  let rec add_or elist = let e, rest = (hd elist), (tl elist) in
  (* the first case is unnecessary anyways *)
    if ((length elist) = 0) then (gen_e (Const'(Sexpr(Bool false)))) else
    if ((length elist) = 1) then (gen_e e) ^"\n" ^ lexit^":\n" else
    gen_e (hd elist) ^ "\n cmp rax, sob_false \njne " ^lexit^"\n" ^ (add_or rest)
  in
  "; Or"^idx ^ add_or elist ^ "; :::end of Or"^idx

and gen_if consts fvars lam_hist eif etn els =
  let gen_e = gen_e consts fvars lam_hist in
  let cif = gen_e eif in
  let ctn = gen_e etn in
  let cls = gen_e els in
  let ifidx = generate_str_idx if_idx in
  let lelse = "Lelse" ^ ifidx in
  let lexit = "lexitIf" ^ ifidx in
  "; If" ^ ifidx ^
    cif ^ "\ncmp rax, sob_false \nje " ^ lelse ^ ctn ^ "\njmp " ^ lexit ^ "\n" ^ lelse ^ ":\n" ^ cls ^ "\n" ^ lexit ^":\n"
  ^ "; :::end of If" ^ ifidx

and gen_seq consts fvars lam_hist elist = fold_left (fun s e -> s^"\n"^(gen_e consts fvars lam_hist e)) "" elist

and gen_const consts c = let idx = get_const_idx c consts in
  "mov rax, const_tbl+"^(string_of_int idx)

  let generate consts fvars e = gen_e consts fvars (-1, -1) e
  (* This function takes the constants table, the free-variables table and a single exprג€™ and
returns a string containing the assembly code representing the evaluation of the exprג€™. *)
end;;

(* ****************************************************************************************** *)
(* ******************************                        ************************************ *)
(* ****************************************************************************************** *)
