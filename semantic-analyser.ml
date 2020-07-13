(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;
open List;;

let tp s = Tag_Parser.tag_parse_expression(Reader.read_sexpr(s))

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) ->  for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     ( for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       ( for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   ( for_all2 expr'_eq args1 args2)
  | Box'(var1), Box'(var2) -> expr'_eq (Var'(var1)) (Var'(var2))
  | BoxGet'(var1), BoxGet'(var2) -> expr'_eq (Var'(var1)) (Var'(var2))
  | BoxSet'(var1,expr1), BoxSet'(var2,expr2) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
  (expr'_eq (expr1) (expr2))
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct
(*
let haannotate_lexical_addresses e = raise X_not_yet_implemented;;

let haannotate_tail_calls e = raise X_not_yet_implemented;;

let habox_set e = raise X_not_yet_implemented;;

let harun_semantics expr = raise X_not_yet_implemented;;

end;; *)
(*  *)
(* annotate vars *)
(*  *)

let stringlist_to_varlist sl =  map (fun s-> Var s) sl
(* let stringlist_to_varlist sl = let vl = [] in
  for i = 0 to  length sl do
    vl @ [Var sl[i]] *)

(* returns i if var is in the parameter list with index i. else returns -1 *)
let rec find_var_in_parlist var vl i =
  if  length vl = 0       then -1                               else
    if var =  nth vl i    then i                                else
      if i+1 <  length vl then find_var_in_parlist var vl (i+1) else
        -1

(* returns (j, i) if var is bound with index (j, i). else returns (-1, -1) *)
let rec find_var_in_boundlist var bl j =
  if  length bl = 0         then (-1, -1)                           else
    let i = find_var_in_parlist var ( nth bl j) 0 in
      if i > -1                 then (j, i)                             else
        if j+1 <  length bl then find_var_in_boundlist var bl (j+1) else
        (-1, -1)

(* add tag to a given var *)
let add_var_tag parlist boundlist var =
  let i = find_var_in_parlist var parlist 0 in
    if i > -1 then VarParam (var, i) else
  let (major, minor) = find_var_in_boundlist var boundlist 0 in
    if major > -1 then VarBound (var, major, minor) else
  VarFree (var);;

(* annotate all vars in a given expr *)
let rec annotate_vars parlist boundlist exp = let annotate = annotate_vars parlist boundlist in
   match exp with
    | Const c -> Const' c
    | Var v -> Var' (add_var_tag parlist boundlist v)
    | If (e1, e2, e3) -> If' ((annotate e1), (annotate e2), (annotate e3))
    | Seq elist -> Seq' ( map annotate elist)
    | Set (e1, e2) -> Set' ((annotate e1), (annotate e2))
    | Def (e1, e2) -> Def' ((annotate e1), (annotate e2))
    | Or elist -> Or' ( map annotate elist)
    | LambdaSimple (slist, body) -> LambdaSimple' (slist, (annotate_vars slist (parlist::boundlist) body) )
    | LambdaOpt (slist, opt, body) -> LambdaOpt' (slist, opt, (annotate_vars (slist@[opt]) (parlist::boundlist) body) )
    | Applic (op, elist) -> Applic' ((annotate op), ( map annotate elist))

let annotate_lexical_addresses e = annotate_vars [] [] e;;

(*  *)
(* annotate_tail_calls *)
(*  *)

let rec mark_tails e = match e with
  | If' (test, e1, e2) -> If' (test, mark_tails e1, mark_tails e2)
  | Or' elist -> Or' (tailed_elist elist)
  | Seq' elist -> Seq' (tailed_elist elist)
  | Applic' (op, elist) -> ApplicTP' (annotate_tail_calls op, map annotate_tail_calls elist)
  | LambdaSimple' (slist, body) ->  LambdaSimple' (slist, mark_tails body)
  | LambdaOpt' (slist, opt, body) -> LambdaOpt' (slist, opt, mark_tails body)
  | expr' -> annotate_tail_calls expr'

and tailed_elist elist = let rev_elist =  rev elist in
   rev ( cons (mark_tails ( hd rev_elist)) (map annotate_tail_calls ( tl rev_elist)))

and annotate_tail_calls e = match e with
  | LambdaSimple' (slist, body) ->  LambdaSimple' (slist, mark_tails body)
  | LambdaOpt' (slist, opt, body) -> LambdaOpt' (slist, opt, mark_tails body)

  | If'(e1, e2, e3) -> If'(annotate_tail_calls e1, annotate_tail_calls e2, annotate_tail_calls e3)
  | Seq'(elist) -> Seq'(map annotate_tail_calls elist)
  | Or'(elist) -> Or'(map annotate_tail_calls elist)
  | Set'(e1, e2) -> Set'(e1, annotate_tail_calls e2)
  | Def'(e1, e2) -> Def'(e1, annotate_tail_calls e2)
  | Applic'(op, elist) -> Applic'(annotate_tail_calls op, map annotate_tail_calls elist)
  | expr' -> expr'

(*  *)
(* box setting *)
(*  *)

let get_lam_body' lam = match lam with
  | LambdaSimple' (_, body) -> body
  | LambdaOpt' (_,_, body) -> body
  | _ -> raise X_this_should_not_happen

let get_lam_slist lam = match lam with
  | LambdaSimple' (l, _) -> l
  | LambdaOpt' (l, opt, _) -> (opt :: l)
  | _ -> raise X_this_should_not_happen

let get_var'_name var = match var with
  | VarFree(name) -> name
  | VarParam(name, _) -> name
  | VarBound(name, _, _) -> name

let get_var'_minor var = match var with
  | VarFree(_) -> raise X_this_should_not_happen
  | VarParam(_, minor) -> minor
  | VarBound(_, _, minor) -> minor

(**** step 1: finding set! occurances ****)
(* given a var and the lambdas covering it, returns the lambda where it's defined *)
let find_defining_lam v scopelist = match v with
  | VarParam(name, _) ->  hd scopelist
  | VarBound(name, maj, min) ->  nth scopelist (maj+1)
  | VarFree(_) -> raise X_this_should_not_happen

(* adds a new threesome to the setlist ONLY if the setlist doesn't already include a var with the same name and defining lambda *)
let add_var_to_setlist t setlist = let (v1, _, defl1) = t in
  let n1 = (get_var'_name v1) in
    if ( exists (fun (v2, _, defl2)-> ((get_var'_name v2) = n1) && (defl1 = defl2)) setlist)
      then setlist else t :: setlist

(* given an expr', looking for all variables being set! in it.
  For each occurance of set!, it adds the following threesome to a list:
  (var, scope list (all lambdas containing it, starting with the local one) , defining lambda)
  finally, it returns this
  (ignores set! of free vars. We have no interest in these) *)
let rec lookup_sets scopelist setslist e = let lookup_sets_here = lookup_sets scopelist setslist in
  match e with
    | If' (e1, e2, e3) -> (lookup_sets_here e1) @ ((lookup_sets scopelist [] e2) @ (lookup_sets scopelist [] e3))
    | Seq' elist ->  lookup_sets_list scopelist setslist elist
    | Or' elist -> (lookup_sets_list scopelist setslist elist)
    | Applic' (op, elist) -> (lookup_sets_list scopelist [] (op::elist))
    | ApplicTP' (op, elist) -> (lookup_sets_list scopelist [] (op::elist))
    | Def' (v, e1) -> lookup_sets_here e1

    | LambdaSimple' (slist, body) -> lookup_sets (e::scopelist) setslist body
    | LambdaOpt' (slist, opt, body)  -> lookup_sets (e::scopelist) setslist body
    | Set' (Var'(v), e2) -> (match v with
      | VarFree(_) -> lookup_sets_here e2
      | _ -> (v, scopelist, find_defining_lam v scopelist) :: (lookup_sets_here e2))
    | _ -> setslist

and lookup_sets_list scopelist setslist elist = ( fold_left (fun setslist e -> (lookup_sets scopelist [] e) @ setslist) setslist elist);;


(**** step 2: finding read occurances for the set!s ****)

(* given an expr' e and a threesome from lookup_sets t, looking for all variables with same name as t, being read in e.
  For each occurance of, it adds the following pair: (var, scope list) to a list
  finally, it returns this
  if we reach a lambda where t's name is redefined, we don't bother to go inside *)
let rec lookup_reads_in_exp scopelist readlist t e = let (wv, sl, dl) = t in
  let wname = get_var'_name wv in (*the name of the set!ted var is all we need for now *)
    let lookup_reads_in_exp_here = lookup_reads_in_exp scopelist readlist t in
      match e with
        | Var'(rv) -> (match rv with
          | VarFree(_) -> readlist (* if it's free it can't be the same var *)
          | VarParam(rname, _) -> if wname = rname then (rv,scopelist) :: readlist
            else readlist
          | VarBound(rname, _, _) -> if wname = rname then (rv, scopelist) :: readlist
            else readlist (* else, if the names are the same, it's both written & read *)
          )
        | LambdaSimple' (slist, body) -> if ( mem wname slist) then readlist (* check if the name is redefined *)
          else lookup_reads_in_exp (e::scopelist) readlist t body (* if not, go deeper inside *)
        | LambdaOpt' (slist, opt, body) -> if ( mem wname (opt::slist)) then readlist
          else lookup_reads_in_exp (e::scopelist) readlist t body

        | If' (e1, e2, e3) -> (lookup_reads_in_exp_here e1) @ ((lookup_reads_in_exp scopelist [] t e2) @ (lookup_reads_in_exp scopelist [] t e3))
        | Seq' elist ->  lookup_reads_in_exp_list scopelist readlist t elist
        | Or' elist -> (lookup_reads_in_exp_list scopelist readlist t elist)
        | Applic' (op, elist) -> (lookup_reads_in_exp_list scopelist [] t (op::elist))
        | ApplicTP' (op, elist) -> (lookup_reads_in_exp_list scopelist [] t (op::elist))
        | Set' (e1, e2) -> (lookup_reads_in_exp_here e2)
        | BoxSet' (v, e1) -> lookup_reads_in_exp_here e1
        | Def' (v, e1) -> lookup_reads_in_exp_here e1
        | _ -> readlist

and lookup_reads_in_exp_list scopelist readlist t elist = ( fold_left (fun readlist e -> (lookup_reads_in_exp scopelist [] t e) @ readlist) readlist elist);;

(* for each threesome t, return a pair of t & all the occurances where t is being read (with their lambdas) *)
let lookup_reads t = let (name, sclist, defl) = t in
  let db = get_lam_body' defl in
    (t, lookup_reads_in_exp [defl] [] t db)

let lookup_reads_for_all setslist =
   map lookup_reads setslist;;


(**** step 3: understand what needs boxing ****)

(* get a write occ and a read occ of a var.  *)
(* check if they share the same lambda. *)
(* If not, check if they share more than 1 lambda (this 1 is defining lambda). That would mean they refer to the same rib in a lexical env.  *)
(* If all is false, boxing is needed - return true  *)
let check_box_criteria (wv, wsl, _) (rv, rsl)  =
(* sharing the same lambda? *)
  if ( hd wsl =  hd rsl) then false else
  (* sharing the same rib in lex. env.? *)
    if ( length ( filter (fun lam ->  mem lam rsl) wsl) > 1)
      then false else true
  (* if (wl = rl) then false
    else match wv, rv with
    | VarBound(_, wmaj, _), VarBound(_,rmaj,_) ->
      if (wmaj > 1) && (rmaj > 1) then false else true
    | _ -> true *)

(* create a list of all the writing occurances of vars meeting the criteria of being box-askers *)
let make_box_asker balist pair = let (wt, rlist) = pair in
  if ( exists (check_box_criteria wt) rlist)
    then (wt :: balist)
    else balist

let box_askers plist =
   fold_left make_box_asker [] plist

(* step 3.5: Going through the balist, create a list of all the lambdas need changing and their box asking vars *)
(* A REALLY UGLY PATCH *)

let add_var_to_vl wv vl lam = let n, minor = get_var'_name wv, get_var'_minor wv in
  if (mem n (map get_var'_name vl))
    then vl
    else let (parted_vl1, parted_vl2) = partition (fun var -> (get_var'_minor var) < minor) vl in
      parted_vl1 @ [wv] @ parted_vl2

let make_lam_var_pair_list lvpl t = let (wv, _, defl) = t in
  let (lvp, rest) = partition (fun (lam, vl) -> lam = defl) lvpl in
    if (length lvp) > 0
      then let (lam, vl) = (hd lvp) in
        (lam, (add_var_to_vl (*get_var'_name*) wv vl lam)) :: rest
      else (defl, [((*get_var'_name*) wv)]) :: rest

let step_35 balist =
  fold_left make_lam_var_pair_list [] balist

(**** step 4: box whatever needs boxing ****)

let rec box_exp lvpl e = let box_exp = box_exp lvpl in
  match e with
  | If'(e1, e2, e3) -> If'(box_exp e1, box_exp e2, box_exp e3)
  | Seq'(elist) -> Seq'(map box_exp elist)
  | Set'(e1, e2) -> Set'(e1, box_exp e2)
  | BoxSet'(v, e2) -> BoxSet'(v, box_exp e2)
  | Or'(elist) -> Or'(map box_exp elist)
  | Applic'(op, elist) -> Applic'(box_exp op, map box_exp elist)
  | ApplicTP'(op, elist) -> ApplicTP'(box_exp op, map box_exp elist)
  | Def'(e1, e2) -> Def'(e1, box_exp e2)
  (* if it's a lambda, let should_lam_box create a new lambda *)
  | LambdaSimple'(slist, body) -> should_lam_box lvpl e
  | LambdaOpt'(slist, opt, body) -> should_lam_box lvpl e
  | _ -> e

(* is the lambda in the box-asking list? *)
and should_lam_box lvpl lam =
  let (lvp, rest) = partition (fun (v_lam, vl) -> lam = v_lam) lvpl in
    if (length lvp) > 0
      then box_lam rest (hd lvp) lam
      (* no need to box this one, but look for inner lambdas *)
      else make_fresh_lambda lam (box_exp lvpl (get_lam_body' lam))

and box_lam lvpl lvp lam =
  let (lam, varl) = lvp in
    let body = get_lam_body' lam in
      let box_seq = map make_box_cmd varl in (* create the sequence for the boxing at the start of the lambda *)
        let boxed_body = fold_right (box_var lvpl) varl body in
          let new_body = Seq'(box_seq @ [boxed_body]) in
            make_fresh_lambda lam new_body

and make_box_cmd v = let n, minor = get_var'_name v, get_var'_minor v in
  (Set'(Var'(VarParam(n, minor)), Box'(VarParam(n, minor))))

and make_fresh_lambda lam new_body = match lam with
  | LambdaSimple'(slist, body) -> LambdaSimple'(slist, new_body)
  | LambdaOpt'(slist, opt, body) -> LambdaOpt'(slist, opt, new_body)
  | _ -> raise X_this_should_not_happen

(* box all occurances of vars with name n in expr' e, unless e is a lambda redefining n. In that case, ignore it *)
and box_var lvpl v e = let box_var, n = (box_var lvpl v), (get_var'_name v) in match e with
(* in case of a var, if it has the same name, that's our get-occurance *)
  | Var'(v) -> if ((get_var'_name v) = n)
                then BoxGet'(v)
                else e
(* in case of a set, if it has the same name, that's our get-occurance *)
  | Set'(e1, e2) -> (match e1 with
    | Var'(v) -> if ((get_var'_name v) = n)
                  then BoxSet'(v, box_var e2)
                  else Set'(e1, box_var e2)
    | _ -> raise X_this_should_not_happen)
   (* in case of a lambda, check if it itself should be boxed and fix its body while it's still pure and innocent *)
   (* after the body is fixed, check if the name is redefined. If so, no need to go inside. if not, go deeper inside *)
  | LambdaSimple' (slist, _) -> let new_lam = should_lam_box lvpl e in
      if ( mem n slist)
        then new_lam
        else LambdaSimple' (slist, box_var (get_lam_body' new_lam) )
  | LambdaOpt' (slist, opt, _) -> let new_lam = should_lam_box lvpl e in
      if ( mem n (opt::slist))
        then new_lam
        else LambdaOpt' (slist, opt, box_var (get_lam_body' new_lam) )

  | BoxSet'(v, e1) -> BoxSet'(v, box_var e1)
  | If'(e1, e2, e3) -> If'(box_var e1, box_var e2, box_var e3)
  | Seq'(elist) -> Seq'( map box_var elist)
  | Or'(elist) -> Or'( map box_var elist)
  | Applic'(op, elist) -> Applic'(box_var op,  map box_var elist)
  | ApplicTP'(op, elist) -> ApplicTP'(box_var op,  map box_var elist)
  |_ -> e

(**** step 5: combine it all together ****)

let box_set e =
  let setlist = lookup_sets [] [] e in
    let plist = lookup_reads_for_all setlist in
      let balist = box_askers plist in
        let patch35 = step_35 balist in
          box_exp patch35 e ;;

let pbs1 e =
  let setlist = lookup_sets [] [] e in
    setlist;;

let pbs2 e =
  let setlist = lookup_sets [] [] e in
    let plist = lookup_reads_for_all setlist in
      plist;;

let pbs3 e =
  let setlist = lookup_sets [] [] e in
    let plist = lookup_reads_for_all setlist in
      let balist = box_askers plist in
        balist;;

let pbs35 e =
  let setlist = lookup_sets [] [] e in
    let plist = lookup_reads_for_all setlist in
      let balist = box_askers plist in
        step_35 balist;;

(* ALREADY GIVEN: DO NOT TOUCH!!! *)
let run_semantics expr =
  box_set
     (annotate_tail_calls
       (annotate_lexical_addresses expr));;

let ltp expr =
   (annotate_tail_calls
       (annotate_lexical_addresses (tp expr)));;

let ltp2 expr =
   (annotate_tail_calls
       (annotate_lexical_addresses ( expr)));;

end;;
(* struct Semantics *)

let rs s = Semantics.run_semantics(tp s)
