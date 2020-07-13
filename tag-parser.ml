(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;
open Reader;;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

(* let tag_parse_expressionHA sexpr = raise X_not_yet_implemented;;

let tag_parse_expressionsHA sexpr = raise X_not_yet_implemented;; *)

(*
end;; (* struct Tag_Parser *)
(* should be deleted: *)
let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;
(***)  *)

(***Helpers and stuff***)
(***********************)
let parse_var sym =
  if (List.mem sym reserved_word_list) then
    raise X_syntax_error
  else
    Var(sym);;

let rec arguments_to_string_list s t =
  (match t with
    | Nil -> [s]
    | Pair(Symbol(ts), tt) -> [s] @ (arguments_to_string_list ts tt)
    | _ -> raise X_syntax_error
  );;

let rec parse_pair f s =
  match f, s with
  (*quotes:*)
    | Symbol("quote"), Pair(x,Nil) ->    Const(Sexpr(x))
  (*conditionals:*)
    | Symbol("if"), Pair(test, Pair(s_then, Nil)) ->  If(tag_parse_expression(test), tag_parse_expression(s_then), Const(Void))
    | Symbol("if"), Pair(test, Pair(s_then, Pair(s_else, Nil))) ->  If(tag_parse_expression(test), tag_parse_expression(s_then), tag_parse_expression(s_else))
  (* lambdas: *)
    | Symbol("lambda"), Pair(Symbol(s), body) -> LambdaOpt([], s, (parse_seq body))
    | Symbol("lambda"),Pair(arguments, body) -> (parse_lambda arguments body)
  (*simple stuff:*)
    | Symbol("or"), _ -> parse_or s
    | Symbol("define"), _ -> parse_define s
    | Symbol("set!"), Pair(Symbol(name), Pair(sexpr, Nil)) -> Set(Var(name), (tag_parse_expression sexpr))
    | Symbol("begin"), _ -> parse_seq s
  (* Macro expansions: *)
    | Symbol("quasiquote"), Pair(x, Nil) -> tag_parse_expression(parse_quasiquote x)
    | Symbol("cond"), _ -> tag_parse_expression(parse_cond s)
    | Symbol("let"), _ -> tag_parse_expression(parse_let s)
    | Symbol("let*"), _ -> tag_parse_expression(parse_letstar s)
    | Symbol("letrec"), _ -> tag_parse_expression(parse_letrec s)
    | Symbol("and"), _ -> tag_parse_expression(parse_and s)
  (*application:*)
    | _, Pair(h,t) -> Applic(tag_parse_expression f, spair_to_elist h t)
    | _, Nil -> Applic(tag_parse_expression f, [])
    | _, t -> Applic(tag_parse_expression f, [tag_parse_expression t])

(* Lambdas *)
and lambda_simple_arguments_to_string_list s t =
  (match t with
    | Nil -> [s]
    | Pair(Symbol(ts), tt) -> [s] @ (lambda_simple_arguments_to_string_list ts tt)
    | _ -> raise X_syntax_error
  )

and lambda_optional_arguments_to_string_list s t =
  (match t with
    | Symbol(last_symbol) -> [s]
    | Pair(Symbol(ts), tt) -> [s] @ (lambda_optional_arguments_to_string_list ts tt)
    | _ -> raise X_syntax_error
  )

and is_lambda_simple s t =
  (match t with
    | Nil -> true
    | Symbol(_) -> false
    | Pair(Symbol(ts), tt) -> (is_lambda_simple ts tt)
    | _ -> raise X_syntax_error
  )

and lambda_optional_get_last s t =
  (match t with
      | Symbol(last_symbol) -> last_symbol
      | Pair(Symbol(ts), tt) -> (lambda_optional_get_last ts tt)
      | _ -> raise X_syntax_error
    )

and parse_lambda arguments body =
  (match arguments with
    | Nil -> LambdaSimple([],(parse_seq body))
    | Pair(Symbol(s),n) ->
      (match (is_lambda_simple s n) with
      | true ->  LambdaSimple((lambda_simple_arguments_to_string_list s n), (parse_seq body))
      | false -> LambdaOpt((lambda_optional_arguments_to_string_list s n),(lambda_optional_get_last s n), (parse_seq body)))
    | _ -> raise X_this_should_not_happen
  )

(* or *)
and parse_or s = match s with
  | Nil -> Const(Sexpr(Bool(false)))
  | Pair(h, Nil) -> tag_parse_expression h
  | Pair(h, t) -> Or(spair_to_elist h t)
  | _ -> raise X_this_should_not_happen

and spair_to_elist h t =
  match t with
    | Pair(t1,t2) -> [tag_parse_expression h] @ (spair_to_elist t1 t2)
    | Nil -> [tag_parse_expression h]
    | (Bool _|Number _|Char _|String _|Symbol _|Vector _) -> [tag_parse_expression h] @ [tag_parse_expression t]

(* seq *)
and parse_seq s = match s with
  | Nil -> Const(Void)
  | Pair(sexpr, Nil) -> tag_parse_expression sexpr
  | Pair(sexpr, t) -> Seq(spair_to_elist sexpr t)
  | _ -> raise X_this_should_not_happen

(* define & MIT define *)
and parse_define s = match s with
  | Pair(Symbol(name), Pair(sexpr, Nil)) -> Def(Var(name), (tag_parse_expression sexpr))
  | Pair (Pair (Symbol(name), arglist),body) -> tag_parse_expression(Pair (Symbol "define",
                                                  Pair (Symbol(name),
                                                    Pair
                                                    (Pair (Symbol "lambda",
                                                      Pair (arglist, body)),
                                                    Nil))))
  | _ -> raise X_syntax_error

(* Macro Expansions *)
and parse_quasiquote s = match s with
| Pair (Symbol "unquote", Pair (sexpr, Nil)) -> sexpr
| Vector(l) -> Pair(Symbol "vector", List.fold_right quasi_vector_to_pair l Nil)
| Pair (Symbol "unquote-splicing", _ ) -> raise X_syntax_error
| Nil | Symbol _ -> Pair (Symbol "quote", Pair(s, Nil))
(* | Symbol(_) -> Pair(Symbol("quote"), Pair(s, Nil)) *)
| Pair(Symbol "quote", Pair(x, Nil)) -> Pair(Symbol "quote", Pair(Pair(Symbol "quote", Pair(x, Nil)), Nil))
| Pair(Pair (Symbol "unquote-splicing", Pair(sexpr, Nil)), b) -> Pair(Symbol "append", Pair(sexpr, Pair(parse_quasiquote b, Nil)))
| Pair(a , Pair (Pair (Symbol "unquote-splicing", Pair(sexpr, cont)), Nil)) -> Pair (Symbol "cons", Pair (parse_quasiquote a, Pair(Pair(Symbol "append", Pair(sexpr, Pair((parse_quasiquote cont), Nil))),Nil)))
| Pair(a , Pair (Symbol "unquote-splicing", Pair(sexpr, Nil))) -> Pair (Symbol "cons", Pair (parse_quasiquote a, Pair(sexpr, Nil)))
| Pair(a, b) -> Pair (Symbol "cons", Pair (parse_quasiquote a, Pair (parse_quasiquote b, Nil)))
| _ -> s


and quasi_vector_to_pair a b =
  Pair(parse_quasiquote a, b)

(* cond *)
and parse_cond s = match s with
  (* Fat Arrow - NOT YET TESTED! *)
  | Pair (Pair(test, Pair(Symbol("=>"), Pair(sexpr, cont))), Nil) -> Pair (Symbol "let",
                                                                      Pair
                                                                        (Pair (Pair (Symbol "value", Pair (test, Nil)),
                                                                          Pair
                                                                          (Pair (Symbol "f",
                                                                            Pair
                                                                              (Pair (Symbol "lambda", Pair (Nil, Pair(
                                            Pair(Symbol("begin"), Pair(sexpr, cont)), Nil))),
                                                                              Nil)),
                                                                          Nil)),
                                                                        Pair
                                                                        (Pair (Symbol "if",
                                                                          Pair (Symbol "value",
                                                                            Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), Nil))),
                                                                        Nil)))
  | Pair (Pair(test, Pair(Symbol("=>"), Pair(sexpr, cont))), rest) -> Pair (Symbol "let",
                                                                      Pair
                                                                        (Pair (Pair (Symbol "value", Pair (test, Nil)),
                                                                          Pair
                                                                          (Pair (Symbol "f",
                                                                            Pair
                                                                              (Pair (Symbol "lambda", Pair (Nil, Pair(
                                            Pair(Symbol("begin"), Pair(sexpr, cont)), Nil))),
                                                                              Nil)),
                                                                          Pair
                                                                            (Pair (Symbol "rest",
                                                                              Pair (Pair (Symbol "lambda", Pair (Nil, Pair (Pair (Symbol "cond", rest), Nil))),
                                                                              Nil)),
                                                                            Nil))),
                                                                        Pair
                                                                        (Pair (Symbol "if",
                                                                          Pair (Symbol "value",
                                                                            Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
                                                                            Pair (Pair (Symbol "rest", Nil), Nil)))),
                                                                        Nil)))
  | Pair (Pair(Symbol "else", elsexprs), _) -> Pair (Symbol "begin", elsexprs)
  | Pair (Pair(test, Pair(sexpr, cont)), Nil) -> Pair (Symbol "if",
                                        Pair (test,
                                          Pair(
                                            Pair(Symbol("begin"), Pair(sexpr, cont)), Nil)))
  | Pair (Pair(test, Pair(sexpr, cont)), rest) -> (Pair (Symbol "if",
                                        Pair (test,
                                          Pair(
                                            Pair(Symbol("begin"), Pair(sexpr, cont)),
                                              Pair(Pair (Symbol "cond", rest), Nil)))))
  | _ -> raise X_syntax_error


(* the let family *)
and parse_let s = match s with
  | Pair(Nil, commands) ->  Pair
                              (Pair (Symbol "lambda",
                                Pair (Nil,
                                  commands)),
                              Nil)
  | Pair(deflist, commands) -> let (varlist, explist) = seperate_letVarlist_to_pairs deflist in
                                Pair
                                  (Pair (Symbol "lambda",
                                    Pair (varlist,
                                      commands)),
                                  explist)
  | _ -> raise X_syntax_error

and parse_letstar s = match s with
    (* (let* () <expr1>...<exprm>) *)
    | Pair(Nil,body) -> Pair(Symbol("let"),Pair(Nil,body))
    (* (let* ((v <Expr1>)) <expr1>...<exprm>) *)
    | Pair(Pair(first_assigning, Nil), body) -> Pair(Symbol("let"),Pair(Pair(first_assigning, Nil), body))
    (* (let* ((v1 <Expr1>)(v2 <Expr2>)...(vn <Exprn>)) <expr1>...<exprm>) *)
    | Pair(Pair(first_assigning, other_assigning), body) -> Pair (Symbol "let",
                                                              Pair (Pair (first_assigning, Nil),
                                                                Pair
                                                                (Pair (Symbol "let*",
                                                                  Pair
                                                                    (other_assigning,
                                                                    body)),
                                                                Nil)))
    | _ -> raise X_this_should_not_happen


and parse_letrec s = match s with
  | Pair(Nil, commands) -> Pair(Symbol("let"), s)
  | Pair(deflist, commands) -> let (namelist, funclist) = seperate_letVarlist_to_pairs deflist in
                                Pair (Symbol "let",
                                  Pair(func_namelist_to_rec_init namelist, funclists_to_rec_setting_and_body namelist funclist commands))
  | _ -> raise X_syntax_error

(* returns a tuple with two sexpr lists: one of the vars and one of their corresponding exprs *)
and seperate_letVarlist_to_pairs s =
match s with
  | Pair(Pair(var, Pair(sexp, Nil)), Nil) -> Pair(var, Nil), Pair(sexp, Nil)
  | Pair(Pair(var, Pair(sexp, Nil)), rest) -> let (varlist, explist) = (seperate_letVarlist_to_pairs rest)
                                    in (Pair(var, varlist), Pair(sexp, explist))
  | _ -> raise X_not_yet_implemented

and func_namelist_to_rec_init namelist = match namelist with
  | Pair(name, Nil) -> Pair(Pair(name, Pair(Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil)), Nil)
  | Pair(name, rest) -> Pair(Pair(name, Pair (Pair(Symbol "quote", Pair (Symbol "whatever", Nil)), Nil)), func_namelist_to_rec_init rest)
  | _ -> raise X_syntax_error

and funclists_to_rec_setting_and_body namelist funclist commands = match namelist, funclist with
  | Pair(name, Nil), Pair(func, Nil) -> Pair(Pair (Symbol "set!", Pair (name, Pair (func, Nil))), commands)
  | Pair(name, restN), Pair(func, restF) -> Pair(Pair (Symbol "set!", Pair (name, Pair (func, Nil))), funclists_to_rec_setting_and_body restN restF commands)
  | _ -> raise X_syntax_error

(* and *)
and parse_and s = match s with
  | Nil -> Bool true
  | Pair(sexp, Nil) -> sexp
  | Pair(sexp1, rest) -> Pair (Symbol "if",
                          Pair (sexp1,
                            Pair (parse_and rest,
                              Pair (Bool false, Nil))))
  | _ -> raise X_syntax_error

and tag_parse_expression sexpr = match sexpr with
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Nil -> Const(Void)
  | Number(x) -> Const(Sexpr(Number(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | String(x) -> Const(Sexpr(String(x)))
  | Symbol(x) -> parse_var x
  | Pair(f, s) -> parse_pair f s
  | Vector(x) -> raise X_not_yet_implemented

let tag_parse_expressions sexprlist = List.map tag_parse_expression sexprlist;;

let tp = tag_parse_expression;;

end ;;