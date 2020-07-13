
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) ->
    if (List.length l1 = List.length l2) then
      List.for_all2 sexpr_eq l1 l2
      else false
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

 (*temporary end*)

(*--------------------------------------------------------------*)
                      (* OUR PC.ML *)
(*--------------------------------------------------------------*)

(* general list-processing procedures *)

let lowercase_ascii  =
  let delta = int_of_char 'A' - int_of_char 'a' in
  fun ch ->
  if ('A' <= ch && ch <= 'Z')
  then char_of_int ((int_of_char ch) - delta)
  else ch;;

let to_lowercase c =
  (List.map lowercase_ascii c);;

let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

let list_to_string s =
  String.concat "" (List.map (fun ch -> String.make 1 ch) s);;

(* the parsing combinators defined here *)

exception X_not_yet_implemented;;

exception X_no_match;;

let const pred =
  function
  | [] -> raise X_no_match
  | e :: s ->
     if (pred e) then (e, s)
     else raise X_no_match;;

let caten nt1 nt2 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  ((e1, e2), s);;

let pack nt f s =
  let (e, s) = (nt s) in
  ((f e), s);;

let nt_epsilon s = ([], s);;

let nt_epsilon_as_char s = ('\000', s);;

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_no_match -> (nt2 s);;

let nt_none _ = raise X_no_match;;

let disj_list nts = List.fold_right disj nts nt_none;;

let nt_end_of_input_as_char = function
  | []  -> ('\000', [])
  | _ -> raise X_no_match;;

let rec star nt s =
  try let (e, s) = (nt s) in
      let (es, s) = (star nt s) in
      (e :: es, s)
  with X_no_match -> ([], s);;

let plus nt =
  pack (caten nt (star nt))
       (fun (e, es) -> (e :: es));;

let not_followed_by nt1 nt2 s =
  match (let ((_, s) as result) = (nt1 s) in
	 try let _ = (nt2 s) in
	     None
	 with X_no_match -> (Some(result))) with
  | None -> raise X_no_match
  | Some(result) -> result;;

let followed_by nt1 nt2 s =
  match (let ((_, s) as result) = (nt1 s) in
	 try let _ = (nt2 s) in
	     Some(result)
	 with X_no_match -> (None)) with
  | None -> raise X_no_match
  | Some(result) -> result;;

let look_but_dont_touch_as_char nt s =
  try (let _ = (nt s) in
    nt_epsilon_as_char s )
  with X_no_match -> raise X_no_match;;

let rec ignore nt1 nt2 s =
  try (let (_, s1) = (nt1 s) in
    (ignore nt1 nt2 s1))
  with X_no_match -> (nt2 s)

let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

(* useful general parsers for working with text *)

let make_char equal ch1 = const (fun ch2 -> equal ch1 ch2);;

let char = make_char (fun ch1 ch2 -> ch1 = ch2);;

let char_ci =
  make_char (fun ch1 ch2 ->
	     (lowercase_ascii ch1) =
	       (lowercase_ascii ch2));;

let make_word char str =
  List.fold_right
    (fun nt1 nt2 -> pack (caten nt1 nt2) (fun (a, b) -> a :: b))
    (List.map char (string_to_list str))
    nt_epsilon;;

let word = make_word char;;

let word_ci = make_word char_ci;;

let nt_whitespace = const (fun ch -> ch <= ' ');;

let ignore_whitespace nt = ignore nt_whitespace nt;;

let make_range leq ch1 ch2 (s : char list) =
  const (fun ch -> (leq ch1 ch) && (leq ch ch2)) s;;

let range = make_range (fun ch1 ch2 -> ch1 <= ch2);;

let range_ci =
  make_range (fun ch1 ch2 ->
	      (lowercase_ascii ch1) <=
		(lowercase_ascii ch2));;

(* testing the parsers *)

let test_string nt str =
  let (e, s) = (nt (string_to_list str)) in
  (e, (Printf.sprintf "->[%s]" (list_to_string s)));;

(*--------------------------------------------------------------*)
                  (* OUR CODE STARTS HERE *)
(*--------------------------------------------------------------*)

exception IllegalChar
let char_to_bool c = match c with
  |'t' -> true
  |'f' -> false
  |_ -> raise IllegalChar;;

(* range with exceptions helpers: *)
let ch_l_neighbor ch = char_of_int((int_of_char ch)-1);;
let ch_r_neighbor ch = char_of_int((int_of_char ch)+1);;
let range_with_exceptions ch1 ch2 ex1 ex2 = disj_list [(range ch1 (ch_l_neighbor ex1)); (range (ch_r_neighbor ex1) (ch_l_neighbor ex2)); (range (ch_r_neighbor ex2) ch2)];;

let dec_digit = range '0' '9';;
let hex_digit = disj (range '0' '9') (range_ci 'a' 'f');;
let lowercase_char = range 'a' 'z';;
let uppercase_char = range 'A' 'Z';;
let special_char = disj_list [(char '!'); (char '$'); (char '^'); (char '*'); (char '-'); (char '_'); (char '='); (char '+'); (char '<'); (char '>'); (char '?'); (char '/'); (char ':')];;
let symbol_char = disj_list [(dec_digit); (lowercase_char); (uppercase_char); (special_char)];;
let char_prefix = word_ci "#\\";;
let named_char = disj_list [(word_ci "nul"); (word_ci "newline"); (word_ci "return"); (word_ci "tab"); (word_ci "page"); (word_ci "space")];;
let visible_char = range (char_of_int 33) (char_of_int 127);;
let hex_char = (caten (char_ci 'x') (plus hex_digit));;
let all_ascii = range '\000' (char_of_int 127);;
let almost_all_ascii = range_with_exceptions '\000' (char_of_int 127) '\003' '\n';;
let auto_balanced = word "...";;
let auto_balanced_as_char = pack (word "...") (fun _ -> '.');;
let closing_paren = (char ')');;
let pair_prefix = disj (char '(') (char '[');;
let pair_postfix = disj (closing_paren) (char ']');;

let num_delim = disj_list [(range ' ' '@'); (range '[' '`'); (followed_by (char_ci 'e') (range '+' '9')); nt_end_of_input_as_char];;

let match_fixes prefix postfix = (prefix = '(' && postfix = ')') || (prefix = '[' && postfix = ']') || (postfix = '.');;
let match_fixes_nested prefix postfix = (prefix = '(' && postfix = Some(')')) || (prefix = '[' && postfix = Some(']')) || (postfix = Some('.')) || (postfix = None);;

(******* OUR CODE STARTS HERE *********)

(*helper functions*)
let list_to_int base nl = match base with
| 10 ->  int_of_string (list_to_string nl)
| 16 ->  Scanf.sscanf (list_to_string nl) "%x" (fun x->x)
| _ -> raise X_this_should_not_happen;;

let parse_as_is s = s;;


let rec whitespace_cleaner = function
  | [] -> []
  | e::s ->
      if (e > ' ') then e::s
        else whitespace_cleaner s;;

let s_to_value_int n = match n with
  |Int(i) -> i
  | _ -> raise X_this_should_not_happen;;

let s_to_value_float n = match n with
    |Float(f) -> f
    | _ -> raise X_this_should_not_happen;;


(*main functions:*)

(*
let dead_space = raise X_not_yet_implemented;;
*)
(*
Bool
*)
let parse_bool b =
  match (lowercase_ascii (snd b)) with
  | 't' -> Bool(true)
  | 'f' -> Bool(false)
  | _ -> raise X_this_should_not_happen ;;

let read_bool =
  pack (caten ( char '#') (disj (char_ci 't') (char_ci 'f'))) parse_bool;;

(*
  Symbol
*)

let read_symbol =
  pack (plus symbol_char)
    (fun c -> (Symbol(list_to_string (to_lowercase c))));;

(*
   Number
*)

let parse_number base n =
  match (fst n) with
  | Some '-' -> (list_to_int base (snd n)) * -1
  | Some '+' -> (list_to_int base (snd n))
  | None -> (list_to_int base (snd n))
  | _ -> raise X_this_should_not_happen

let parse_int base n =
  Int(
    parse_number base n  );;

(* read_int_based should get a combinator that recognizes digits on the required base, and an int indicating the base *)
let read_int_based digits base =
  pack (caten
    (maybe (disj (char '-') (char '+')))
    (plus (digits)))
  (parse_int base);;

(* taking care of decimal numbers: *)
let read_int_dec =
  read_int_based dec_digit 10;;

let read_int_hex s =
    let (e,n) = (caten (char '#') (char_ci 'x') s) in
    (read_int_based hex_digit 16 n);;

let parse_int_as_float base sign s = float_of_int (parse_number (int_of_float base) (sign, s));;

let parse_float base n =
  let (sign, (lNum, (p, rNum))) = n in
    match sign with
    | Some ('+')| None ->
      Float (
        (parse_int_as_float base sign lNum) +.
        ((parse_int_as_float base None rNum) /. (base ** (float_of_int (List.length rNum))))    )
    | Some ('-') ->
      Float (
        (parse_int_as_float base sign lNum) -.
        ((parse_int_as_float base None rNum) /. (base ** (float_of_int (List.length rNum))))    )
    | _ -> raise X_this_should_not_happen;;

let read_float_based digits base =
  pack (caten
    (maybe (disj (char '-') (char '+')))
    (caten
      (plus digits)
        (caten (char '.')
          (plus digits))))
  (parse_float base );;

let read_float_dec =
   read_float_based dec_digit 10.0;;

let read_float_hex s =
  let (e,n) = (caten (char '#') (char_ci 'x') s) in
  (read_float_based hex_digit 16.0 n);;

let read_number =
  pack (not_followed_by
        (disj_list [read_float_dec; read_float_hex; read_int_hex; read_int_dec])
          (read_symbol))
    (fun (num) -> Number(num));;


(*
  char
*)

let parse_named_char c =
  match (list_to_string (to_lowercase c)) with
  | "nul" -> Char(char_of_int 0)
  | "newline" -> Char(char_of_int 10)
  | "return" -> Char(char_of_int 13)
  | "tab" -> Char(char_of_int 9)
  | "page" -> Char(char_of_int 12)
  | "space" -> Char(char_of_int 32)
  | _ -> raise X_this_should_not_happen;;

let read_named_char =
  pack (caten char_prefix named_char)
    (fun (_, c) -> (parse_named_char c));;

let read_visible_char =
  pack (caten char_prefix visible_char)
    (fun (_, c) -> (Char(c)));;

let parse_hex_char c =
  (list_to_int 16 (List.filter (fun x -> ( (x!='#') && (x!='\\') &&(x!='x'))) c));;

let read_hex_char =
  pack (caten char_prefix hex_char)
    (fun (_, (x, c)) -> Char(char_of_int(parse_hex_char c)));;

let read_char = disj_list[(read_hex_char); (read_named_char); (read_visible_char);];;

(*
  String
*)

let stringLiteralChar =
  let chars = range_with_exceptions (Pervasives.char_of_int 0) (Pervasives.char_of_int 127) '\"' '\\' in
    pack (chars) (fun s -> s);;

let parse_metaChar c =
  match c with
  | 'r' -> '\r'
  | 'n' -> '\n'
  | 't' -> '\t'
  | 'f' -> '\012'
  | '\\' -> '\\'
  | '\"' -> '\"'
  | _ -> raise X_this_should_not_happen;;

let stringMetaChar =
  let chars = [(char '\\'); (char '\"'); (char_ci 't'); (char_ci 'f'); (char_ci 'n'); (char_ci 'r') ] in
    pack (caten (char '\\') (disj_list chars))
      (fun (sl, ch) -> parse_metaChar ch);;

let stringHexChar =
  pack (caten (char '\\')
          (caten (char_ci 'x')
            (caten (plus hex_digit)
              (char ';'))))
    (fun (_, (_, (hex, _))) ->
      (char_of_int (Scanf.sscanf (list_to_string hex) "%x" (fun x->x)) ));;

let stringChar =
  star (disj_list [stringLiteralChar; stringMetaChar; stringHexChar]);;

let read_string =
  pack (caten (char '\"')
      (caten stringChar (char '\"')))
    (fun (_, (s, _)) -> String(list_to_string s) );;

(*
  sexpr
*)

let rec sexpr_nt  chl = let newChl = whitespace_cleaner chl in
  pack (ignore dead_space_for_nil_nt
    (disj_list [expansions; read_nil; read_bool; read_number; read_string; read_char; read_list; read_vector; read_quoted; read_symbol; ]) )
    (fun sexpr-> sexpr) newChl

(*
Pair
*)

and read_list chl = let newChl = whitespace_cleaner chl in
  pack (disj
        (caten (pair_prefix)
              (caten read_occ_list
              (ignore dead_space_for_nil_nt
                  (pair_postfix)      )))
        (caten (pair_prefix)
              (caten read_occ_n_list
              (ignore dead_space_for__nested_nil_nt
                  (auto_balanced_as_char)      ))))
    (fun (prefix, (pair, postfix )) ->
      if match_fixes prefix postfix then
        pair
      else raise PC.X_no_match ) newChl
      (* pair) newChl*)

and read_occ_list chl =
  pack (caten sexpr_nt
        (disj read_occ_list read_list_end))
    (fun (sexpr, list) -> Pair(sexpr, list) ) chl

and read_undotted_end chl =
  pack  nt_epsilon
  (fun sexpr -> Nil) chl
(*  pack (followed_by sexpr_nt (char ')')) *)

and read_dotted_end chl =
  pack  (caten (ignore dead_space_for_nil_nt(char '.'))
          sexpr_nt)
  (fun (dot, sexp) -> sexp) chl

and read_list_end chl =
  pack (disj
          read_dotted_end
          read_undotted_end)
  (fun sexpr -> sexpr) chl

(*
  Vector
*)
and read_vector chl =
  pack (disj
      (caten (word "#(")
        (caten (star (sexpr_nt))
        (ignore dead_space_for_nil_nt (closing_paren))  ))
       (caten (word "#(")
        (caten (star (nested_sexpr_nt))
        (ignore dead_space_for__nested_nil_nt (auto_balanced_as_char))  )))
  (fun (_, (vec, _)) -> Vector(vec)) chl

(*
  quoted forms
*)
and normal_quoted chl =
  pack (caten (char '\'')
        (sexpr_nt))
  (fun (_, sexpr) -> (Symbol("quote"), Pair(sexpr, Nil)))
  chl

and qquoted_quoted chl =
  pack (caten (char '`')
        (sexpr_nt))
  (fun (_, sexpr) -> (Symbol("quasiquote"), Pair(sexpr, Nil)))
  chl

and unquotedSpliced_quoted chl =
  pack (caten (word ",@")
        (sexpr_nt))
  (fun (_, sexpr) -> (Symbol("unquote-splicing"), Pair(sexpr, Nil)))
  chl

and unquoted_quoted chl =
  pack (caten (char ',')
        (sexpr_nt))
  (fun (_, sexpr) -> (Symbol("unquote"), Pair(sexpr, Nil)))
  chl

and read_quoted chl =
  pack (disj_list [normal_quoted; qquoted_quoted; unquotedSpliced_quoted; unquoted_quoted])
  (fun (name, pair) -> Pair(name, pair))
  chl

(*
  dead spaces
*)

and line_comment_nt chl =
  pack
  (caten (char ';')
  (caten (star almost_all_ascii)
  (char '\n')))
  (function (_)-> ()) chl

and whitespaces_nt chl =
  pack( plus (nt_whitespace))
  (function (_)-> ()) chl
  
and sexpr_comment_nt chl =
  pack(
    ignore_whitespace
    (caten (char '#')
    (caten (char ';')
    (caten (star (sexpr_comment_nt))
    (sexpr_nt)  ))))
  (function (_)-> ())
    chl

and auto_balanced_nt chl =
  pack (auto_balanced)
  (function (_)-> ()) chl

and dead_space_nt chl = disj_list [whitespaces_nt; line_comment_nt; sexpr_comment_nt; auto_balanced_nt] chl
and dead_space_for_nil_nt chl = disj_list [whitespaces_nt; line_comment_nt; sexpr_comment_nt] chl

(*
  nil
*)

and read_nil chl =
  pack (disj
        (caten (char '(')
          (caten (star dead_space_for_nil_nt)
          (closing_paren)))
        (caten (char '(')
          (caten (star dead_space_for_nil_nt)
          (auto_balanced_as_char))))
  (fun _-> Nil) chl

(**************** Nested occurances: ****************)

(*
  Nested sexpr
*)

and nested_sexpr_nt  chl = let newChl = whitespace_cleaner chl in
  pack (ignore dead_space_for_nil_nt
    (disj_list [expansions; read_bool; read_number; read_string; read_char; read_n_list; read_n_vector; read_n_quoted; read_n_nil; read_symbol; ]) )
    (fun sexpr-> sexpr) newChl

(*
Nested Pair
*)

and read_n_list chl = let newChl = whitespace_cleaner chl in
  pack (caten (pair_prefix)
              (caten read_occ_n_list
              (ignore dead_space_for_nil_nt
                  (maybe pair_postfix)      )))
    (fun (prefix, (pair, postfix )) ->
      if match_fixes_nested prefix postfix then
        pair
      else raise PC.X_no_match ) newChl

and read_occ_n_list chl =
  pack (caten nested_sexpr_nt
        (disj read_occ_n_list read_list_n_end))
    (fun (sexpr, list) -> Pair(sexpr, list) ) chl

and read_undotted_n_end chl =
  pack  nt_epsilon
  (fun sexpr -> Nil) chl

and read_dotted_n_end chl =
  pack  (caten (ignore dead_space_for_nil_nt(char '.'))
          nested_sexpr_nt)
  (fun (dot, sexp) -> sexp) chl

and read_list_n_end chl =
  pack (disj
          read_dotted_n_end
          read_undotted_n_end)
  (fun sexpr -> sexpr) chl

(*
  Vector
*)
and read_n_vector chl =
  pack (caten (word "#(")
        (caten (star (nested_sexpr_nt))
        (ignore dead_space_for_nil_nt (maybe closing_paren))  ))
  (fun (_, (vec, _)) -> Vector(vec)) chl

(*
  quoted forms
*)
and normal_n_quoted chl =
  pack (caten (char '\'')
        (nested_sexpr_nt))
  (fun (_, sexpr) -> (Symbol("quote"), Pair(sexpr, Nil)))
  chl

and qquoted_n_quoted chl =
  pack (caten (char '`')
        (nested_sexpr_nt))
  (fun (_, sexpr) -> (Symbol("quasiquote"), Pair(sexpr, Nil)))
  chl

and unquotedSpliced_n_quoted chl =
  pack (caten (word ",@")
        (nested_sexpr_nt))
  (fun (_, sexpr) -> (Symbol("unquote-splicing"), Pair(sexpr, Nil)))
  chl

and unquoted_n_quoted chl =
  pack (caten (char ',')
        (nested_sexpr_nt))
  (fun (_, sexpr) -> (Symbol("unquote"), Pair(sexpr, Nil)))
  chl

and read_n_quoted chl =
  pack (disj_list [normal_n_quoted; qquoted_n_quoted; unquotedSpliced_n_quoted; unquoted_n_quoted])
  (fun (name, pair) -> Pair(name, pair))
  chl

and sexpr_comment_n_nt chl =
  pack(
    ignore_whitespace
    (caten (char '#')
    (caten (char ';')
    (caten (star (sexpr_comment_nt))
    (nested_sexpr_nt)  ))))
  (function (_)-> ())
    chl

and dead_space_for__nested_nil_nt chl = disj_list [whitespaces_nt; line_comment_nt; sexpr_comment_n_nt] chl

(*
  nil
*)

and read_n_nil chl =
  pack (caten (char '(')
        (caten (star dead_space_for_nil_nt)
        (maybe closing_paren)))
  (fun _-> Nil) chl

(*
  Additions and expansions:
*)
and expansions chl =
  pack (disj_list [read_scientific_notation_int; read_scientific_notation_float]  )
  (fun x-> x)
  chl

and read_scientific_notation_int chl=
  pack (caten (disj read_int_dec read_int_hex)
        (caten (char_ci 'e')
        (disj read_int_dec read_int_hex)))
  (fun (n1, (e, n2))-> Number(Float(
    (float_of_int (s_to_value_int n1)) *. (10.0 ** (float_of_int (s_to_value_int n2))))))
  chl

and read_scientific_notation_float chl=
  pack (caten (disj read_float_dec read_float_hex)
        (caten (char_ci 'e')
        (disj read_int_dec read_int_hex)))
  (fun (n1, (e, n2))-> Number(Float(
    (s_to_value_float n1) *. (10.0 ** (float_of_int (s_to_value_int n2))))))
  chl

;;


(*
AND LAST:
*)

let read_sexpr string =
  let (sexpr, rest) = sexpr_nt (string_to_list string) in
    sexpr;;

let sexprs_nt chl =
  pack (star (((ignore dead_space_nt) sexpr_nt)))
  (fun s_list -> s_list) chl ;;

let read_sexprs string =
  let (sexprs_list, nothing) = sexprs_nt (string_to_list string) in
    sexprs_list

end;;  (*  struct Reader *)
