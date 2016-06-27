(* compiler.ml
 * A compiler from Scheme to CISC
 *
 * Programmers: Alex Stoliar and Orian Zinger, 2015
*)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_WTF;;
exception X_this_should_not_happen;;

let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

  let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;   

  let string_to_list str =
  let rec loop i limit =
  if i = limit then []
else (String.get str i) :: (loop (i + 1) limit)
in
loop 0 (String.length str);;

let list_to_string s =
  let rec loop s n =
  match s with
  | [] -> String.make n '?'
  | car :: cdr ->
  let result = loop cdr (n + 1) in
  String.set result n car;
  result
in
loop s 0;;

type fraction = {numerator : int; denominator : int};;

type number =
| Int of int
| Fraction of fraction;;

type sexpr =
| Void
| Bool of bool
| Nil
| Number of number
| Char of char
| String of string
| Symbol of string
| Pair of sexpr * sexpr
| Vector of sexpr list;;

module type SEXPR = sig
val sexpr_to_string : sexpr -> string
end;; (* signature SEXPR *)

module Sexpr : SEXPR = struct

open PC;;

exception X_invalid_fraction of fraction;;

let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
   (fun ch -> (ch = (Char.lowercase ch)))
 s) then str
else Printf.sprintf "|%s|" str;;

let string_of_bool b =
  match b with
  |false -> "#f"
  |true -> "#t"
;;

let rec sexpr_to_string sexpr = 
  match sexpr with
  | Pair ((Symbol "quasiquote"), Pair (Symbol qq, Nil)) -> "`" ^ qq
  | Pair ((Symbol "unquote"), Pair (Symbol uq, Nil)) -> "," ^ uq
  | Void -> ""
  | Bool (b) -> string_of_bool b
  | Number (Int n) ->  (string_of_int n)
  | Number (Fraction {numerator = num; denominator = denom}) -> 
  (string_of_int num) ^ "/" ^ (string_of_int denom)
  | Nil -> "()"
  | Char c -> (list_to_string [c])
  | String str -> str
  | Symbol sym -> sym 
  | Pair (car,cdr) -> "(" ^ (string_of_pair car cdr) ^ ")"
  | Vector v -> "#(" ^ (string_of_vector v)  ^ ")"
  (*| _ -> raise X_no_match*)

  and string_of_pair car cdr =
  let car_string = (sexpr_to_string car) in
  let cdr_string = match cdr with
  | Nil -> ""
  | Pair (nested_car, nested_cdr) -> (string_of_pair nested_car nested_cdr)
  | _ -> " . "  ^ (sexpr_to_string cdr) in 
  car_string ^ " " ^ cdr_string 

  and string_of_vector v = 
  match v with
  | [] -> ""
  | _ ->  (sexpr_to_string (List.hd v)) ^ " " ^ (string_of_vector (List.tl v));;

end;; (* struct Sexpr *)

module type PARSER = sig
val read_sexpr : string -> sexpr
val read_sexprs : string -> sexpr list
end;;

module Parser : PARSER = struct

open PC;;

let nt_bool =
let nt_true = pack (word_ci "#t") (fun (_) -> (Bool true)) in
let nt_false = pack (word_ci "#f") (fun (_) -> (Bool false)) in
let nt = disj nt_false nt_true in
nt ;;

let nt_void s = 
  match s with
  | ['V';'o';'i';'d'] -> (Void,[' '])
  | _ -> raise X_no_match;;

  let nt_whtSpcStar = star nt_whitespace;;
  let wrapWithBool nt = (pack nt (fun _ -> true));;

  let make_char_value base_char displacement =
  let base_char_value = Char.code base_char in
  fun ch -> (Char.code ch) - base_char_value + displacement;;

  let nt_digits = 
  let nt = range '0' '9' in
  let nt = pack nt (make_char_value '0' 0) in
  let nt = plus nt in
  let nt = pack nt (fun s -> List.fold_left (fun a b -> a * 10 + b) 0 s) in
  nt;;

  let nt_digits_with_hexa = 
  let nt_dec = range '0' '9' in
  let nt_dec = pack nt_dec (make_char_value '0' 0) in
  let nt_not_cap = range 'a' 'f' in
  let nt_not_cap = pack nt_not_cap (make_char_value 'a' 0xa) in
  let nt_cap = range 'A' 'F' in
  let nt_cap = pack nt_cap (make_char_value 'A' 0xA) in
  let nt = disj_list [nt_dec ; nt_cap ; nt_not_cap] in
  let nt = plus nt in
  let nt = pack nt (fun s -> List.fold_left (fun a b -> a * 16 + b) 0 s) in
  nt;;

  let nt_hexa = 
  let nt = caten (word_ci "0x") nt_digits_with_hexa in
  let nt = pack nt (fun (_,digits) -> digits) in
  nt;;

  let nt_int s = 
  let nt = char '-' in
  let nt = pack nt (fun e -> -1) in
  let nt' = char '+' in
  let nt' = pack nt' (fun e -> 1) in
  let nt = disj nt nt' in
  let nt = maybe nt in
  let nt = pack nt (function | None -> 1 | Some(mult) -> mult) in
  let nt_dec = caten nt nt_digits in
  let nt_hex = caten nt nt_hexa in
  let nt = disj nt_hex nt_dec in
  let nt = pack nt (fun (mult, n) -> Number(Int (mult * n))) in
  nt s;;

  let nt_int_for_fraction_dec = 
  let nt = char '-' in
  let nt = pack nt (fun e -> -1) in
  let nt' = char '+' in
  let nt' = pack nt' (fun e -> 1) in
  let nt = disj nt nt' in
  let nt = maybe nt in
  let nt = pack nt (function | None -> 1 | Some(mult) -> mult) in
  let nt = caten nt nt_digits in
  let nt = pack nt (fun (mult, n) -> (mult * n)) in
  nt;;

  let nt_int_for_fraction_hex = 
  let nt = char '-' in
  let nt = pack nt (fun e -> -1) in
  let nt' = char '+' in
  let nt' = pack nt' (fun e -> 1) in
  let nt = disj nt nt' in
  let nt = maybe nt in
  let nt = pack nt (function | None -> 1 | Some(mult) -> mult) in
  let nt = caten nt nt_hexa in
  let nt = pack nt (fun (mult, n) -> (mult * n)) in
  nt;;

  let rec gcd num denom = 
  if denom = 0 then num
else gcd denom (num mod denom);;

let nt_fraction_handler num denom=
if (denom = 0) then raise X_no_match 
else let the_gcd = (gcd num denom) in
if the_gcd = denom then Number(Int (num / denom))
else Number(Fraction ({numerator = num / (abs the_gcd) ;  denominator = denom / (abs the_gcd)}));;

let nt_fraction_handler_dec s = 
  let nt = caten nt_int_for_fraction_dec (char '/') in
  let nt = pack nt (fun (num,_) -> num) in
  let nt = caten nt nt_digits in
  let nt = pack nt (fun (num,denom)-> (nt_fraction_handler num denom) ) in
  nt s;;

  let nt_fraction_handler_hexa s = 
  let nt = caten nt_int_for_fraction_hex (char '/') in
  let nt = pack nt (fun (num,_) -> num) in
  let nt = caten nt nt_digits_with_hexa in
  let nt = pack nt (fun (num,denom)-> (nt_fraction_handler num denom) ) in
  nt s;;

  let nt_fraction s =
  let nt = disj nt_fraction_handler_hexa nt_fraction_handler_dec in
  nt s;;

  let nt_digit = range '0' '9';;
  let nt_lower = range 'a' 'z';;
  let nt_upper = range 'A' 'Z';;
  let nt_punc = disj_list [char '!' ; char '$' ; char '^' ; char '*' ; char '-' ; char '_' ; char '=' ; char '+' ; char '<' ; char '>' ; char '/' ; char '?'];;

  let nt_num s =
  let nt_first = disj nt_fraction nt_int in
  let nt_crap = (plus (disj_list [nt_lower ; nt_upper ; nt_punc])) in
  let nt = diff nt_first (caten nt_first nt_crap) in
  nt s;;

  let nt_symbol = 
  let nt_letters = pack (disj nt_lower nt_upper) (fun l -> Char.lowercase l) in
  let nt = (plus (disj_list [nt_letters ; nt_digit ; nt_punc])) in
  let nt = pack nt (fun sym -> Symbol(list_to_string sym)) in
  nt;;

  let nt_string_meta_n = pack (word "\\n") (fun (_) -> '\n');;
  let nt_string_meta_r = pack (word "\\r") (fun (_) -> '\r');;
  let nt_string_meta_t = pack (word "\\t") (fun (_) -> '\t');;
  let nt_string_meta_f = pack (word "\\f") (fun (_) -> '\012');;
  let nt_string_meta_back_slash = pack (word "\\\\") (fun (_) -> '\\');;

  let nt_string_meta = disj_list [nt_string_meta_n ; nt_string_meta_r ; nt_string_meta_t ; nt_string_meta_f ; nt_string_meta_back_slash];;

  let nt_chars = 
  let nt = diff nt_any (one_of "\\\"") in
  let nt = disj nt nt_string_meta in
  let nt = star nt in
  nt;;

  let nt_string = 
  let nt = caten (word "\"") nt_chars in  
  let nt = pack nt (fun (_,chars) -> chars) in
  let nt = caten nt (word "\"") in
  let nt = pack nt (fun (chars,_) -> chars) in
  let nt = pack nt list_to_string in
  let nt = pack nt (fun str -> String str) in
  nt;;


  let nt_char_meta_newline = pack (word_ci "newline") (fun (_) -> '\n');;
  let nt_char_meta_return = pack (word_ci "return") (fun (_) -> '\r');;
  let nt_char_meta_tab = pack (word_ci "tab") (fun (_) -> '\t');;
  let nt_char_meta_page = pack (word_ci "page") (fun (_) -> '\012');;
  let nt_char_meta_space = pack (word_ci "space") (fun (_) -> ' ');;

  let nt_char_meta = disj_list [nt_char_meta_newline ; nt_char_meta_return ; nt_char_meta_tab ; nt_char_meta_page ; nt_char_meta_space];;

  let nt_char_handler = 
  let nt = diff nt_any (one_of "\\\"") in
  let nt = disj nt_char_meta nt in
  nt;;

  let nt_char = 
  let nt = caten (word "#\\") nt_char_handler in  
  let nt = pack nt (fun (_,c) -> Char c) in
  nt;;

  let rec nt_sexpr s =
  let listWithoutCrap = List.map removeSkiped [nt_void; nt_bool; nt_nil ; nt_num ; nt_symbol ; nt_char ; nt_string ; nt_pair ; nt_vector ; nt_quotes] in
  let chooseParser = disj_list listWithoutCrap in
  chooseParser s

  and nt_lineComnt s= 
  let semicolon = (char ';') in
  let nt3 = diff nt_any (char '\n') in
  let anyStar = (star nt3) in
  let endLine = disj (char '\n') (pack nt_end_of_input (fun _ -> '\n')) in
  let nt = caten nt_whtSpcStar semicolon in
  let nt = pack nt (fun (ws,chr) -> chr) in
  let nt = caten nt anyStar in
  let nt = pack nt (fun (smclon,any) ->  "")  in
  let nt = caten nt endLine in 
  let nt = pack nt (fun (_,endLne) ->  "")  in
  nt s


  and nt_sexprComnt s= 
  let nt = caten (word "#;") nt_sexpr in
  nt s

  and removeSkiped nt s = 
  let starRemove = (star nt_rmv) in
  let nt' = caten starRemove nt in
  let nt' = pack nt' (fun (ws,op) -> op) in
  let nt' = caten nt' starRemove in
  let nt' = pack nt' (fun (op, ws) -> op) in
  nt' s

  and nt_rmv s=
  let nt = disj_list [(wrapWithBool nt_whitespace);(wrapWithBool nt_lineComnt);(wrapWithBool nt_sexprComnt)] in
  nt s


  and nt_nil s= 
  let nt = caten (char '(') (star nt_rmv)  in
    let nt = pack nt (fun (leftParent,crap) -> leftParent) in
    let nt = caten nt (char ')') in
  let nt = pack nt (fun (crap,rightParent) -> Nil) in
  nt s 

  and nt_pair s=
  let nt = caten  (char '(') (star nt_sexpr) in
    let nt = pack nt (fun (_,sex) -> sex) in
  let nt1 = char ')' in
  let nt1 = pack nt1 (fun _ -> Nil) in 
  
  let nt2 = caten nt_sexpr (char ')') in
let nt3 = caten  (char '.') nt2 in
let nt2 = pack nt3 (fun (_, (sex, _)) ->sex) in

let nt1 = disj nt1 nt2 in

let nt = caten nt nt1 in
let nt = pack nt (fun (s, e) ->
  List.fold_right 
  (fun a b -> Pair(a,b))
  s
e) in
nt s

and nt_vector s = 
let nt = caten (word "#(") (star nt_sexpr) in
  let nt = pack nt (fun (_,vec) -> vec) in
  let nt = caten nt (char ')') in
let nt = pack nt (fun (vec,_) -> (Vector vec)) in
nt s

and nt_quote s= 
let nt = caten (word "'") nt_sexpr in
let nt = pack nt (fun (_,sex) -> (Pair ((Symbol "quote") , Pair(sex , Nil)))) in
nt s

and nt_quasiquote s = 
let nt = caten (word "`") nt_sexpr in
let nt = pack nt (fun (_,sex) -> (Pair ((Symbol "quasiquote") , Pair(sex , Nil)))) in
nt s

and nt_unquotedSpliced s = 
let nt = caten (word ",@") nt_sexpr in
let nt = pack nt (fun (_,sex) -> (Pair ((Symbol "unquote-splicing") , Pair(sex , Nil)))) in
nt s

and nt_unquote s = 
let nt = caten (word ",") nt_sexpr in
let nt = pack nt (fun (_,sex) -> (Pair ((Symbol "unquote") , Pair(sex , Nil)))) in
nt s

and nt_quotes s = disj_list [nt_quote ; nt_quasiquote ; nt_unquotedSpliced ; nt_unquote] s;;

let read_sexpr string =  
  match (nt_sexpr (string_to_list string)) with 
  |(a,[]) ->a
  |(a,_) -> raise X_no_match;; 

  let read_sexprs string =
  let stl = string_to_list string in
  let rec helper stl =  
  match  (nt_sexpr stl) with
  |(frst,[]) -> [frst]
  |(frst,rest) -> frst::(helper rest) in
  helper stl;;

end;; (* struct Parser *)


open PC;;



(* work on the tag parser starts here *)

(* from assignment 2*)
(*
type expr =
  | Const of sexpr
  | Var of string  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list)
  | ApplicTP of expr * (expr list);;
*)

(*new - assignment 3*)
type expr =
| Const of sexpr
| Var of string  
| If of expr * expr * expr
| Seq of expr list
| Set of expr * expr
| Def of expr * expr
| Or of expr list
| LambdaSimple of string list * expr
| LambdaOpt of string list * string * expr
| Applic of expr * (expr list)

exception X_syntax_error;;

module type TAG_PARSER = sig
val read_expression : string -> expr
val read_expressions : string -> expr list
val expression_to_string : expr -> string
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
["and"; "begin"; "cond"; "define"; "do"; "else";
"if"; "lambda"; "let"; "let*"; "letrec"; "or";
"quasiquote"; "quote"; "set!"; "unquote";
"unquote-splicing"];;  

let rec symHelper sym l=
if l = [] 
then (Var sym) 
else (if ((List.hd l) = sym ) 
  then raise X_syntax_error 
else (symHelper sym (List.tl l)));;

let rec process_scheme_list s ret_nil ret_one ret_several =
  match s with
  | Nil -> ret_nil ()
  | (Pair(sexpr, sexprs)) ->
  process_scheme_list sexprs
  (fun () -> ret_one sexpr)
  (fun sexpr' -> ret_several [sexpr; sexpr'])
  (fun sexprs -> ret_several (sexpr :: sexprs))
  | _ -> raise X_syntax_error;;
  
  let scheme_list_to_ocaml_list args = 
  process_scheme_list args
  (fun () -> [])
  (fun sexpr -> [sexpr])
  (fun sexprs -> sexprs);;

  let ocaml_list_to_scheme_list l = List.fold_right (fun a b -> (Pair (a,b))) l Nil;;

  let expand_let_star ribs sexprs =
  let ribs = scheme_list_to_ocaml_list ribs in
  let params = List.map (function
   | (Pair(name, (Pair(expr, Nil)))) -> name
 | _ -> raise X_this_should_not_happen) ribs in
  let args = List.map
  (function
   | (Pair(name, (Pair(expr, Nil)))) -> expr
 | _ -> raise X_this_should_not_happen) ribs in
  let params_set = List.fold_right
  (fun a s ->
    if (ormap
     (fun b ->
      (match (a, b) with
       | (Symbol a, Symbol b) -> a = b
     | _ -> raise X_this_should_not_happen))
   s)
  then s else a :: s)
  params
  [] in
  let place_holders = List.fold_right
  (fun a s -> Pair(a, s))
  (List.map
    (fun var -> (Pair(var, (Pair((Bool false), Nil)))))
  params_set)
  Nil in
  let assignments = List.map2
  (fun var expr ->
   (Pair((Symbol("set!")),
     (Pair(var, (Pair(expr, Nil)))))))
  params args in
  let body = List.fold_right
  (fun a s -> Pair(a, s))
  assignments
  sexprs in
  (Pair((Symbol("let")), (Pair(place_holders, body))));;

  let expand_letrec ribs sexprs =
  let ribs = scheme_list_to_ocaml_list ribs in
  let params = List.map (function
   | (Pair(name, (Pair(expr, Nil)))) -> name
 | _ -> raise X_this_should_not_happen) ribs in
  let args = List.map
  (function
   | (Pair(name, (Pair(expr, Nil)))) -> expr
 | _ -> raise X_this_should_not_happen) ribs in
  let ribs = List.map
  (function
   | (Pair(name, (Pair(expr, Nil)))) ->
   (Pair(name, (Pair(Bool false, Nil))))
 | _ -> raise X_this_should_not_happen)
  ribs in
  let body = List.fold_right
  (fun a s -> Pair(a, s))
  (List.map2
    (fun var expr ->
     (Pair((Symbol("set!")),
      (Pair(var, (Pair(expr, Nil)))))))
  params args)
  sexprs in
  let ribs = List.fold_right
  (fun a s -> Pair(a, s))
  ribs
  Nil in
  (Pair((Symbol("let")), (Pair(ribs, body))));;

  exception X_unquote_splicing_here_makes_no_sense;;

  let expand_let ribs sexpr = raise X_not_yet_implemented;;

  (*macro-expander for the quasiquoted expressions*)
  let rec expand_qq sexpr = match sexpr with
  | (Pair((Symbol("unquote")), (Pair(sexpr, Nil)))) -> sexpr
  | (Pair((Symbol("unquote-splicing")), (Pair(sexpr, Nil)))) ->
  raise X_unquote_splicing_here_makes_no_sense
  | (Pair(a, b)) ->
  (match (a, b) with
    | ((Pair((Symbol("unquote-splicing")), (Pair(a, Nil)))), b) ->
    let b = expand_qq b in
    (Pair((Symbol("append")),
      (Pair(a, (Pair(b, Nil))))))
    | (a, (Pair((Symbol("unquote-splicing")), (Pair(b, Nil))))) ->
    let a = expand_qq a in
    (Pair((Symbol("cons")), (Pair(a, (Pair(b, Nil))))))
    | (a, b) ->
    let a = expand_qq a in
    let b = expand_qq b in
    (Pair((Symbol("cons")), (Pair(a, (Pair(b, Nil)))))))
  | (Vector(sexprs)) ->
  let s = expand_qq (List.fold_right (fun a b -> Pair(a, b)) sexprs Nil) in
  (Pair((Symbol("list->vector")), (Pair(s, Nil))))
  | Nil | Symbol _ -> (Pair((Symbol("quote")), (Pair(sexpr, Nil))))
  | expr -> expr;;

(*(Printf.printf "#%s#%s" (Sexpr.sexpr_to_string procedure) (Sexpr.sexpr_to_string sexprs)) *)
  let tag_parse sexpr = 
  let rec tpHelper sexpr = 
  match sexpr with 
  | Bool _ | Number _ | Nil | Void | Char _ | String _ | Vector _ -> Const sexpr
  | (Pair ((Symbol "let"), (Pair (ribs, sexprs)))) -> (letHelper ribs sexprs)
  | (Pair ((Symbol "let*"), (Pair (ribs, sexprs)))) ->  (tpHelper (expand_let_star ribs sexprs))
  | (Pair ((Symbol "letrec"), (Pair (ribs, sexprs)))) -> (tpHelper (expand_letrec ribs sexprs))
  | (Pair ((Symbol "define"), (Pair ((Pair (def_name, def_argl), def_value))))) ->
  (tpHelper (Pair ((Symbol "define"), (Pair (def_name, (Pair ((Pair ((Symbol "lambda"), (Pair(def_argl, def_value)))), Nil)))))))
  | (Pair ((Symbol "quote"), Pair ((q, Nil)))) -> (Const q)
  | (Pair ((Symbol "quasiquote"), Pair ((q, Nil)))) -> (tpHelper (expand_qq q))
  | (Pair ((Symbol "cond"), args)) -> (cndHelper args)
  | (Pair ((Symbol "and"), pr)) -> (andHelper pr) 
  | (Pair ((Symbol "if"), (Pair (pred, Pair(do_if_true, Nil))))) -> (If ((tpHelper pred), (tpHelper do_if_true), (Const Void)))
  | (Pair ((Symbol "if"), (Pair (pred, Pair(do_if_true, (Pair (do_if_false, Nil))))))) -> (If ((tpHelper pred), (tpHelper do_if_true), (tpHelper do_if_false)))
  | (Pair ((Symbol "define"), Pair (def_name, Pair (def_value, Nil)))) -> (dfnHelper def_name def_value)
  | (Pair ((Symbol "set!"),  Pair (set_name, Pair (set_value, Nil)))) -> (Set ((tpHelper set_name), (tpHelper set_value)))
  | (Pair ((Symbol "lambda"),Pair (args, sexprs))) -> (chooseLambda (lambdaArgHandler args) (lambdaBodyHandler sexprs))
  | (Pair ((Symbol "begin"), sexprs)) -> bgnHelper sexprs
  | (Pair ((Symbol("or")), sexprs))-> orHelper sexprs
  | (Pair (procedure,sexprs)) ->  (Applic ((tpHelper procedure), (List.map tpHelper (scheme_list_to_ocaml_list sexprs))))
  | (Symbol sym) -> (symHelper sym reserved_word_list)


  and letHelper ribs sexprs = 
  let ribs = scheme_list_to_ocaml_list ribs in
  let params = List.map (function
    | (Pair(name, (Pair(expr, Nil)))) -> name
  | _ -> raise X_this_should_not_happen) ribs in
  let args = List.map
  (function
   | (Pair(name, (Pair(expr, Nil)))) -> expr
 | _ -> raise X_this_should_not_happen) ribs in
  (Applic ((chooseLambda (lambdaArgHandler (ocaml_list_to_scheme_list params)) (bgnHelper sexprs)) , (List.map tpHelper args)))

  and andHelper pr = 
  match pr with
  | Nil -> (Const (Bool true))
  | (Pair (arg, Nil)) -> tpHelper arg
  | (Pair (arg, Pair (do_if_true, Nil))) -> If (tpHelper arg, tpHelper do_if_true, (Const (Bool false)))
  | (Pair (arg, rest)) -> let s = tpHelper arg in If  (s ,tpHelper (Pair ((Symbol "and"), rest)), (Const (Bool false)) )
  | _ -> raise X_no_match

  and cndHelper args =
  match args with
  | Pair (Pair (Symbol "else", Nil), Nil) -> (Const Void)
  | Pair (Pair (Symbol "else", rest), Nil) -> (tpHelper rest)
  | Pair ((Pair (t, e)), Nil) -> If ( tpHelper t, bgnHelper e, (Const Void))
  | Pair ((Pair (t, e)), rest) -> If (tpHelper t, bgnHelper e, tpHelper (Pair ((Symbol "cond"), rest)))
  | Nil -> Const Void
  | _ -> raise X_syntax_error

  and dfnHelper name value = 
  match name with
  | (Symbol sym) ->  (Def ((tpHelper name), (tpHelper value)))
  | _ -> raise X_no_match

  and lambdaBodyHandler sexprs = 
  let sList = (Pair ((Symbol "begin"), sexprs)) in
  let lst = (flattenBegin (scheme_list_to_ocaml_list sList)) in
(*  let ([dfn_lst ; bdy_lst]) = (build_letrec lst [] []) in*)
  let (dfn_lst, bdy_lst) = (build_letrec lst [] []) in
(*  let lst = (build_letrec lst [] []) in
  let dfn_lst = if lst = [] then [] else List.hd lst in
  let bdy_lst = if lst = [] then [] else List.hd (List.tl lst) in*)
  let ribs = ocaml_list_to_scheme_list dfn_lst in
  let body = ocaml_list_to_scheme_list bdy_lst in
  let letrec_exp = if dfn_lst == [] then (Pair ((Symbol "begin"), body)) else (Pair ((Symbol "letrec"), (Pair (ribs, body)))) in
  tpHelper letrec_exp

and build_letrec lst dfn_lst bdy_lst = 
  if lst == [] then raise X_this_should_not_happen else
    let car = List.hd lst in
    let cdr = List.tl lst in
    if (Sexpr.sexpr_to_string car) = "begin" then (build_letrec cdr dfn_lst bdy_lst) else
      match car with
      | (Pair ((Symbol "define"), (Pair ((Pair (def_name, def_argl), def_value))))) ->
   let reg_define = (Pair ((Symbol "define"), (Pair (def_name, (Pair ((Pair ((Symbol "lambda"), (Pair(def_argl, def_value)))), Nil)))))) in
   (build_letrec (reg_define::cdr) dfn_lst bdy_lst)
      | (Pair ((Symbol "define"), Pair (def_name, Pair (def_value, Nil)))) -> let rib = Pair (def_name, Pair (def_value, Nil)) in
                        if cdr == [] then raise X_this_should_not_happen else (build_letrec cdr (dfn_lst@[rib]) cdr)
      | _ -> (dfn_lst , lst)

and flattenBegin sexprs = 
  match sexprs with
  | Pair ((Symbol "begin"), bgnSexprs)::restSexprs -> flattenBegin ((scheme_list_to_ocaml_list bgnSexprs)@(flattenBegin restSexprs))
  | [] -> []
  | notBegin::bgn -> notBegin::(flattenBegin bgn)
         
and bgnHelper sexprs = 
  process_scheme_list sexprs
          (fun () -> Const Void)
          (fun sex -> tpHelper sex)
          (fun sexes -> Seq (List.map tpHelper sexes))
          
and orHelper sexprs =
  process_scheme_list sexprs
          (fun () -> Const (Bool false))
          (fun sex -> tpHelper sex)
          (fun sexes -> Or (List.map tpHelper sexes))
          
and chooseLambda args sexprs =
  let  (a,b)= args in
  match b with
  | Nil -> (LambdaSimple (a,sexprs))
  | (Symbol b) -> (LambdaOpt (a,b,sexprs))
  | _ -> raise X_this_should_not_happen
         
and lambdaArgHandler args = 
  match args with 
  | Nil -> ([],Nil)
  | Pair((Symbol frst),rest) -> 
     let (frstOfRest,restofRest) = (lambdaArgHandler rest) in
     (frst::frstOfRest,restofRest)
  | _ -> ([],args)
     
  in tpHelper sexpr;;
    

let read_expression string = tag_parse (Parser.read_sexpr string);;

let read_expressions string = List.map tag_parse (Parser.read_sexprs string);;

let string_of_bool b =
  match b with
  |false -> "#f"
  |true -> "#t"
;;

let rec expression_to_string expr = 
  match expr with
  | Const (String str) -> "\"" ^ str ^ "\""
  | Const (Char c) ->  char_expttostr c 
  | Const (Bool b) -> string_of_bool b
  | Const (Number (Int num)) -> string_of_int num
  | Const Nil -> "'()"
  | Const Void -> ""
  | Const b -> "'" ^ Sexpr.sexpr_to_string b
  | Var v -> v
  | (If (pred, do_if_true, (Const Void))) -> "(if " ^ (expression_to_string pred) ^ " " ^ (expression_to_string do_if_true) ^ ")"
  | (If (pred, do_if_true, do_if_false)) -> "(if " ^ (expression_to_string pred) ^ " " ^ (expression_to_string do_if_true) ^ " " ^ (expression_to_string do_if_false) ^ ")"
  | (Def (name, value)) -> "(define " ^ (expression_to_string name) ^ " " ^ (expression_to_string value) ^ ")"
  | (Set (name, value)) -> "(set! " ^ (expression_to_string name) ^ " " ^ (expression_to_string value) ^ ")"
  | (Seq lst) -> "(begin " ^ String.concat " " (List.map expression_to_string lst) ^ ")"
  | (Or lst) -> "(or " ^ String.concat " "(List.map expression_to_string lst) ^ ")"
  | (LambdaSimple (a,sexprs)) -> "(lambda (" ^  (String.concat " " a) ^ ") " ^ (expression_to_string sexprs) ^ ")"
  | (LambdaOpt ([], a, b)) -> "(lambda "  ^ a ^ " " ^ expression_to_string b ^ ")"
  | (LambdaOpt (l, a, b)) -> "(lambda (" ^ (String.concat " " l) ^ " . " ^ a ^ ") " ^ expression_to_string b ^ ")"
  | (Applic (procedure, sexprs)) -> "(" ^ (expression_to_string procedure)  ^ " " ^ (String.concat " " (List.map expression_to_string sexprs)) ^ ")"

  and char_expttostr c = 
  match c with
  | '\012' ->  "#\\page"
  | '\r' -> "#\\return"
  | '\t' -> "#\\tab"
  | '\n' ->  "#\\newline"
  | ' ' ->  "#\\space"
  | _ ->  "#\\" ^ Char.escaped c
;;

end;; (* struct Tag_Parser *)

let test_parser string =
  let expr = Tag_Parser.read_expression string in
  let string' = (Tag_Parser.expression_to_string expr) in
  Printf.printf "%s\n" string';;

  type var = 
  | VarFree' of string
  | VarParam' of string * int
  | VarBound' of string * int * int;;

  type expr' =
  | Const' of sexpr
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

  module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

(* PRINT expr' expr'_to_string*)
let rec p_helper expr = 
  match expr with
  | Const' (String str) -> "\"" ^ str ^ "\""
  | Const' (Char c) ->  char_expttostr c 
  | Const' (Bool b) -> string_of_bool b
  | Const' (Number (Int num)) -> string_of_int num
  | Const' Nil -> "'()"
  | Const' Void -> ""
  | Const' b -> "'" ^ Sexpr.sexpr_to_string b
  | BoxGet' (VarFree' s) -> s
  | BoxGet' (VarParam' (s, _)) -> s
  | BoxGet' (VarBound' (s ,_ ,_)) -> s
  | Box' (VarFree' s) -> s
  | Box' (VarParam' (s, _)) -> s
  | Box' (VarBound' (s ,_ ,_)) -> s
  | BoxSet' ((VarFree' s), exp )-> "(BoxSet' " ^ " " ^ s ^ " " ^ p_helper exp ^ ")"
  | BoxSet' ((VarParam' (s ,_)), exp) -> "(BoxSet' " ^  s ^ " " ^ p_helper exp ^ ")"
  | BoxSet' ((VarBound' (s ,_ ,_)), exp) -> "(BoxSet' " ^  s ^ " " ^ p_helper exp ^ ")"
  | Var' (VarFree' s) -> s
  | Var' (VarParam' (s, _)) -> s
  | Var' (VarBound' (s ,_ ,_)) -> s
  | (If' (pred, do_if_true, (Const' Void))) -> "(if " ^ (p_helper pred) ^ " " ^ (p_helper do_if_true) ^ ")"
  | (If' (pred, do_if_true, do_if_false)) -> "(if " ^ (p_helper pred) ^ " " ^ (p_helper do_if_true) ^ " " ^ (p_helper do_if_false) ^ ")"
  | (Def' (name, value)) -> "(define " ^ (p_helper name) ^ " " ^ (p_helper value) ^ ")"
  | (Set' (name, value)) -> "(set! " ^ (p_helper name) ^ " " ^ (p_helper value) ^ ")"
  | (Seq' lst) -> "(begin " ^ String.concat " " (List.map p_helper lst) ^ ")"
  | (Or' lst) -> "(or " ^ String.concat " "(List.map p_helper lst) ^ ")"
  | (LambdaSimple' (a,sexprs)) -> "(lambda (" ^  (String.concat " " a) ^ ") " ^ (p_helper sexprs) ^ ")"
  | (LambdaOpt' ([], a, b)) -> "(lambda "  ^ a ^ " " ^ p_helper b ^ ")"
  | (LambdaOpt' (l, a, b)) -> "(lambda (" ^ (String.concat " " l) ^ " . " ^ a ^ ") " ^ p_helper b ^ ")"
  | (Applic' (procedure, sexprs)) -> "(" ^ (p_helper procedure)  ^ " " ^ (String.concat " " (List.map p_helper sexprs)) ^ ")"
  | (ApplicTP' (procedure, sexprs)) -> "(" ^ (p_helper procedure)  ^ " " ^ (String.concat " " (List.map p_helper sexprs)) ^ ")"


  and char_expttostr c = 
  match c with
  | '\012' ->  "#\\page"
  | '\r' -> "#\\return"
  | '\t' -> "#\\tab"
  | '\n' ->  "#\\newline"
  | ' ' ->  "#\\space"
  | _ ->  "#\\" ^ Char.escaped c
;;

    let p p1 p2 = Printf.printf "!!%s!! %s\n" p1 p2;;
    let pl p1 p2 = List.map (fun a -> Printf.printf "!!%s!! %s\n" p1 a) p2;;
    let plt p1 p2 = List.map (fun a -> Printf.printf "!!%s!! %s\n" p1 (p_helper a)) p2;;

module Semantics : SEMANTICS = struct

(*------------------------------------------start of  4.2 --------------------------------------------------*)
let annotate_lexical_addresses e =
  let rec run_ala e env scope = 
    match e with
    | Var v -> 
        (if inScope v scope then let minor = (findMinor v scope) in Var' (VarParam' (v,minor))
        else if inEnv v env then let (major,minor) = (findMajorAndMin v (List.rev env)) in Var' (VarBound' (v, major, minor))
        else Var' (VarFree' v))
    | (Const b) -> Const' b
    | (If (pred, dit, dif)) -> (If' (run_ala pred env scope, run_ala dit env scope, run_ala dif env scope))
    | (Def (name, value)) -> Def' (run_ala name env scope, run_ala value env scope)
    | (Set (name, value)) -> Set' (run_ala name env scope, run_ala value env scope)
    | (Seq lst) -> Seq' (List.map (fun exp -> run_ala exp env scope) lst)
    | (Or lst) -> Or' (List.map (fun exp -> run_ala exp env scope) lst)
    | (LambdaSimple (a,sexprs)) -> (LambdaSimple' (a,run_ala sexprs (env@[scope]) a))
    | (LambdaOpt ([], a, b)) -> (LambdaOpt' ([], a, run_ala b (env@[scope]) [a]))
    | (LambdaOpt (l, a, b)) -> (LambdaOpt' (l, a, run_ala b (env@[scope]) (l@[a])))
    | (Applic (procedure, sexprs)) -> Applic' (run_ala procedure env scope, List.map (fun exp -> run_ala exp env scope) sexprs)

(*checks if v is in scope*)
and inScope v scope = ormap (fun vInList -> v = vInList) scope 
(*checks if v is in env*)
and inEnv v env = ormap (fun scope -> (inScope v scope)) env 

(*finds and returns the index of v in scope scp*)
and countVar_scp scp v i=
  match scp with
  | [] -> i
  | car::cdr -> if car = v then i else (countVar_scp cdr v (i + 1))

and findMinor v scope = countVar_scp scope v 0

and countVar_env v env maj min =
  (*let print = Printf.printf "!!countVar!! %s" env in *)
  match env with
  | [] -> (maj,min)
  | car::cdr -> if inScope v car then (maj,(countVar_scp car v min)) else countVar_env v cdr (maj + 1) 0

and findMajorAndMin v env = countVar_env v env 0 0

  in run_ala e [] [];;

(*------------------------------------------end of  4.2/start of 4.3 ---------------------------------------------*)

let rdc_rac exprs =
  let rev_exprs = List.rev exprs in
  let last = List.hd rev_exprs in
  let rest_rev = List.tl rev_exprs in
  let rest = List.rev rest_rev in
  (rest,last);;

let annotate_tail_calls e = 
  let rec run e in_tail =
match e with
| Const' _ | Var' _ -> e
| Box' _ | BoxGet' _ | BoxSet' _ -> raise X_this_should_not_happen
| If'(test, dit, dif) -> (If' (run test false, run dit in_tail, run dif in_tail))
| Seq' expers -> let (all_but_last, last) = (rdc_rac expers) in Seq' ((List.map (fun e -> run e false) all_but_last) @ [(run last in_tail)])
| Set' (Var' v, exp) -> Set' (Var' v, run exp false)
| Def' (Var' v, exp) -> Def' (Var' v, run exp false)
| Or' expers -> let  (all_but_last, last) = (rdc_rac expers) in Or' ((List.map (fun e -> run e false) all_but_last) @ [(run last in_tail)])
| LambdaSimple' (pars, exp) -> LambdaSimple' (pars, run exp true)
| LambdaOpt' (pars, opt,exp) -> LambdaOpt' (pars, opt,run exp true)
| Applic' (proc, args) -> if in_tail then ApplicTP' ((run proc false), (List.map (fun e -> run e false ) args) )
else Applic' ( (run proc false), (List.map (fun e -> run e false ) args) )
| _ -> raise X_no_match
   in run e false;;

(*------------------------------------------end of  4.3/start of 4.4 --------------------------------------------------*)

(* box any procedure parameter that meets the needed criteria *)
(* val box_set : expr' -> expr' *)
let box_set e = 
  let rec run_box_set e = 
    match e with 
    | BoxSet' (var, exp) -> BoxSet' (var, run_box_set exp)
    | If'(test, dit, dif)-> If'(run_box_set test, run_box_set dit, run_box_set dif) 
    | Seq' expLst -> Seq' (List.map (fun exp -> run_box_set exp) expLst)
    | Set' (Var' v, exp) -> Set' (Var' v, run_box_set exp)
    | Def' (Var' v, exp) -> Def' (Var' v, run_box_set exp)
    | Or' expLst -> Or' (List.map (fun exp -> run_box_set exp) expLst)
    | LambdaSimple' (params, expr)  -> LambdaSimple'(params, rmvSeq (run_box_set (run_box_helper params expr [])))
    | LambdaOpt' (params, optPar, expr) -> LambdaOpt'(params,optPar, rmvSeq (run_box_set (run_box_helper (params@[optPar]) expr [])))
    | Applic' (proc, args) -> Applic' (run_box_set proc, List.map (fun arg -> run_box_set arg) args)
    | ApplicTP' (proc, args) -> ApplicTP' (run_box_set proc, List.map (fun arg -> run_box_set arg) args)
    | _ -> e
       
  and rmvSeq exp = 
  match exp with
  | Seq' [e] -> e 
  |  _ -> exp  
      
and boxAllParams expr paramsToBox = 
  let new_expr = replaceGetAndSetForAllParams paramsToBox expr in
let setsList = List.map (fun param -> addSet param expr) paramsToBox in
Seq' (setsList@[run_box_set new_expr])
     
and replaceGetAndSetForAllParams paramsToBox expr  = 
  match paramsToBox with
| [] -> expr
| car::cdr -> let expr_new = replaceGetAndSet car expr in replaceGetAndSetForAllParams cdr expr_new 
                           
  and run_box_helper params expr paramsToBox = 
    match params with
    | [] -> (boxAllParams expr paramsToBox) 
    | car::cdr -> let boolBoxParam = shouldBeBoxed car expr in run_box_helper cdr expr (if boolBoxParam  then (paramsToBox@[car]) else paramsToBox) 
                        
  (* if need to box - box. else return expr as is. *)
  and shouldBeBoxed param expr = let (con1,con2,con3) = scan param expr (false,false,false) in
         (con1 && con2 && con3)

  (* returns true if need to box. else returns false. *)
  (*begin Printf.printf "$$FALSE$$"; true; end*)
  and scan param e (con1,con2,con3) = 
    match e with
    | Set' (Var' (VarBound' (par, _, _)), exp) -> if par = param then scan param exp (true,true,con3) else scan param exp (con1,con2,con3)(*bound and set*) 
    | Set' (Var' (VarParam' (par, _)), exp) -> if par = param then scan param exp (con1,true,con3) else scan param exp (con1,con2,con3)(* set*)
    | Var' (VarBound' (par, _, _)) -> if par = param then (true,con2,true) else (con1,con2,con3) (*bound and get*)
    | Var' (VarParam' (par, _)) -> if par = param then (con1,con2,true) else (con1,con2,con3)  (*get*)
    | BoxSet' (_,exp) -> scan param exp (con1,con2,con3)
    | If'(test, dit, dif)-> checkCons param (test::dit::dif::[]) (con1,con2,con3)
    | Seq' seqLst -> checkCons param seqLst (con1,con2,con3)
    | Set' (Var' v, exp) -> scan param exp (con1,con2,con3)
    | Def' (Var' v, exp) -> scan param exp (con1,con2,con3)
    | Or' expLst -> checkCons param expLst (con1,con2,con3)
    | LambdaSimple' (params, exp)  ->  if List.mem param params then (false,false,false) else scan param exp (con1,con2,con3)
    | LambdaOpt' (params, optPar,exp) -> if List.mem param params || List.mem param [optPar] then (false,false,false) else scan param exp (con1,con2,con3)
    | Applic' (proc, args) -> checkCons param (proc::args) (con1,con2,con3)
    | ApplicTP' (proc, args) ->  checkCons param (proc::args) (con1,con2,con3)
    | _ -> (con1,con2,con3)
       
  (* checks if there param apears in params of lambda*)
  (*and checkParam params param= andmap (fun par -> par = param) params*)
       
  and checkCons param expLst (con1,con2,con3) = 
    match expLst with
    | [] -> (con1,con2,con3)
    | (car::cdr) -> let (newCon1,newCon2,newCon3) = scan param car (con1,con2,con3) in checkCons param cdr (newCon1,newCon2,newCon3)
                             
  and  maxFromList l m = (*l for list and m for max*)
  match l with
  | [] -> m
  | car::cdr -> let new_m = Pervasives.max m car in maxFromList cdr new_m
                
and findMinorForSet param e = 
    match e with
    | Set' (Var' (VarBound' (par, _, mi)), _) -> if par = param then mi else (-1)
    | Set' (Var' (VarParam' (par, mi)), _) -> if par = param then mi else (-1)
    | Var' (VarBound' (par, _, mi)) -> if par = param then mi else (-1)
    | Var' (VarParam' (par, mi)) ->  if par = param then mi else (-1)
    | Box' (VarParam' (par, mi)) -> if par = param then mi else (-1)
    | BoxGet' bGet -> findMinorForSet param (Var' bGet)
    | BoxSet' (bSet,exp) -> maxFromList [(findMinorForSet param (Var' bSet)) ; (findMinorForSet param exp)] (-1) 
    | If'(test, dit, dif)-> maxFromList [(findMinorForSet param test) ; (findMinorForSet param dit) ; (findMinorForSet param dif)] (-1)
    | Seq' seqLst -> maxFromList (List.map (fun exp -> findMinorForSet param exp) seqLst) (-1)
    | Set' (v, exp) -> maxFromList [(findMinorForSet param v) ; (findMinorForSet param exp)] (-1)
    | Def' (v, exp) -> maxFromList [(findMinorForSet param v) ; (findMinorForSet param exp)] (-1)
    | Or' expLst -> maxFromList (List.map (fun exp -> findMinorForSet param exp) expLst) (-1)
    | LambdaSimple' (params, exp)  -> findMinorForSet param exp
    | LambdaOpt' (params, optPar,exp) -> findMinorForSet param exp
    | Applic' (proc, args) |ApplicTP' (proc, args) -> maxFromList ((findMinorForSet param proc)::(List.map (fun arg -> findMinorForSet param arg) args)) (-1)
    | _ -> -1
        
  and addSet param expr= 
    let minor = findMinorForSet param expr in
    let varParam = (VarParam' (param, minor)) in
    let add = Set' (Var' varParam, (Box' varParam)) in
    add

  and replaceGetAndSet param expr =  
    match expr with 
    | Set' (Var' (VarBound' (par, mj, mi)), exp) -> if par = param then BoxSet' ((VarBound' (par, mj, mi)), (replaceGetAndSet param exp)) else Set' (Var' (VarBound' (par, mj, mi)), (replaceGetAndSet param exp))
    | Set' (Var' (VarParam' (par, mi)), exp) ->  if par = param then BoxSet' ((VarParam' (par, mi)), (replaceGetAndSet param exp)) else Set' (Var' (VarParam' (par, mi)), (replaceGetAndSet param exp))
    | Var' (VarBound' (par, mj, mi)) -> if par = param then BoxGet' (VarBound' (par, mj, mi)) else expr
    | Var' (VarParam' (par, mi)) -> if par = param then BoxGet' (VarParam' (par, mi)) else expr
    | BoxSet' (v,exp) -> BoxSet' (v ,(replaceGetAndSet param exp)) 
    | If'(test, dit, dif)-> If' ((replaceGetAndSet param test), (replaceGetAndSet param dit), (replaceGetAndSet param dif))
    | Seq' seqLst -> Seq' (List.map (fun exp -> (replaceGetAndSet param exp)) seqLst)
    | Def' (v, exp) -> Def' (v, (replaceGetAndSet param exp))
    | Or' expLst -> Or' (List.map (fun exp -> replaceGetAndSet param exp) expLst)
    | LambdaSimple' (params, exps)  -> if List.mem param params then LambdaSimple' (params, exps) else LambdaSimple' (params, replaceGetAndSet param exps)
    | LambdaOpt' (params, optPar,exps) -> if List.mem param params || List.mem param [optPar] then LambdaOpt' (params, optPar, exps) else LambdaOpt' (params, optPar, replaceGetAndSet param exps)
    | Applic' (proc, args) -> Applic' ((replaceGetAndSet param proc) , List.map (fun arg -> (replaceGetAndSet param arg)) args)
    | ApplicTP' (proc, args) -> ApplicTP' ((replaceGetAndSet param proc) , List.map (fun arg -> (replaceGetAndSet param arg)) args)
    | _ -> expr
       
  in run_box_set e;;
  
let run_semantics expr = 
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)

(*======================================== PROJECT ========================================*)

module type CODE_GEN = sig 
val code_gen : expr' -> string
val compile_scheme_file : string -> string -> unit
 end;;

(*TODO: don't forget to delete the (**) *)
 module Code_Gen (*: CODE_GEN *)= struct
(*------------------------------------------------------*)
(* define addresses*)

type 'a ref = { mutable contents : 'a };;
let ct_start_address = 1000;; (*start of const table*)
let const_end_address = ref ct_start_address;; (* end fo const table*)
let varfree_end_address = ref 0;;
(*let address = ref ct_start_address;; (* end fo const table*) *)
let constParams = ref 0;;
let cur_address = ref 0;;
let pointer = ref 0;; (* TODO DONT NEED THIS*)

let addr_void = string_of_int (ct_start_address);;
let addr_nil = string_of_int (ct_start_address + 1);;
let addr_true = string_of_int (ct_start_address + 2);;
let addr_false = string_of_int (ct_start_address + 4);;
(* !x;;   ---->  - : int = 1 *)
(* x := !x + 1;;   ---->  - : unit = ()*)
(* !x;;   ---->  - : int = 2 *)

(*--------------------------FILE HANDLERS---------------------------*)
    
let file_to_string input_file =
  let in_channel = open_in input_file in
  let rec run () =
    try 
      let ch = input_char in_channel in ch :: (run ())
    with End_of_file ->
      ( close_in in_channel;
        [] )
  in list_to_string (run ());;
  
let string_to_file output_file out_string =
  let out_channel = open_out output_file in
  ( output_string out_channel out_string;
    close_out out_channel );;

(*--------------------- Label generators---------------------*)
(*
# make_if_labels();;
- : string * string = ("L_if_else_1", "L_if_end_1")
# make_if_labels();;
- : string * string = ("L_if_else_2", "L_if_end_2")
*)

  let make_make_label name =
  let counter = ref 0 in
  fun () -> ( counter := !counter + 1; Printf.sprintf "%s_%d" name (!counter) )

let make_if_labels =
  let make_if_else = make_make_label "L_if_else" in
  let make_if_end = make_make_label "L_if_end" in
  fun () ->
  (make_if_else(), make_if_end());;
  
let make_or_labels = make_make_label "L_or_end";;

let make_closure_labels =
  let make_closure_code = make_make_label "L_closure_code" in
  let make_closure_end = make_make_label "L_closure_end" in
  fun () ->
  (make_closure_code(), make_closure_end());;
  
(*Continue*)
let make_cont_labels = make_make_label "L_cont";;

let make_loop_labels =
  let make_loop_code = make_make_label "L_loop_code" in
  let make_loop_end = make_make_label "L_loop_end" in
  fun () ->
  (make_loop_code(), make_loop_end());;


(* --------------------OUR CODE: ------------------------- *)

let callsWrapper str = 
  let withHead = "\n\tPUSH(FP);\n\tMOV(FP, SP);\n" ^ str in
  let withHeadAndTail = withHead ^ "\tPOP(FP);\n\tRETURN;\n" in
  withHeadAndTail;;
(*
let incadrs oldadrs = 
  let inc = cur_address := (oldadrs + 1) in
  (oldadrs - 1);;
*)

  (* 0 for addres, 1 for cur_address*)
(*let incadrs oldadrs inc_by changeFlag =
	let tochange = if changeFlag == 0 then const_end_address else cur_address in
	let inc = tochange := (oldadrs + inc_by) in
	oldadrs;; *)


let incadrs oldadrs inc_by changeFlag =
	let tochange = match changeFlag with
				   | 0 -> const_end_address
				   | 1 -> varfree_end_address
				   | 2 -> cur_address
           | _ -> raise X_this_should_not_happen in
	(* let tochange = if changeFlag == 0 then const_end_address else cur_address in *)
	(*let inc = tochange := (oldadrs + inc_by) in *)
	tochange := (oldadrs + inc_by);(!tochange - inc_by);;

(* =========================== Lib functions ( run time support) =========================== *)

let rec find_func_addrs toFind var_free_table =
  match var_free_table with
  | [] -> raise X_this_should_not_happen
  | (func_name, func_addr) :: cdr -> if toFind = func_name then string_of_int func_addr else find_func_addrs toFind cdr;;


let getConstAddress e const_table = 
  let rec run e const_table = 
    match const_table with
    | [] -> -1
    | frst :: rst -> match frst with
                     | Void,adrs,lst -> if Void = e then adrs else run e rst
                     | Bool b,adrs,lst -> if (Bool b) = e then adrs else run e rst
                     | Nil,adrs,lst -> if Nil = e then adrs else run e rst 
                     | Number (Int n),adrs,lst -> if (Number (Int n)) = e then adrs else run e rst
                     | Number (Fraction {numerator; denominator}),adrs,lst-> if (Number (Fraction {numerator; denominator})) = e then adrs else run e rst
                     | Char c,adrs,lst -> if (Char c) = e then adrs else run e rst
                     | String s,adrs,lst -> if (String s) = e then adrs else run e rst
                     | Symbol s,adrs,lst -> if (Symbol s) = e then adrs else run e rst
                     | Pair (a,b),adrs,lst -> if (Pair (a,b)) = e then adrs else run e rst
                     | Vector v,adrs,lst ->  if (Vector v) = e then adrs else run e rst
                     (*| _ -> run e rst *)
in string_of_int (run e const_table);;


let wrap_rts_clos l_prim_something = 
  let before =   
"\tPUSH(IMM(3));
\tCALL(MALLOC);
\tDROP(1);
\tMOV(IND(R0),IMM(T_CLOSURE)); // Closure 
\tMOV(INDD(R0,1),IMM(496351)); // Dummy env
\tMOV(INDD(R0,2),IMM(LABEL(" in
  let after = "))); // address of Label\n" in
  before ^ l_prim_something ^ after

(* ++++++++++++++++++++++++++++++++++ cons ++++++++++++++++++++++++++++++ *)
let rts_cons var_free_table  =
  (* let update_address = cur_address := !const_end_address in *)
  let opcomnt = "\n\t/* ++++++++++++ cons ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ cons ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_cons:" in
  let addr_in_var_free_table = find_func_addrs "cons" var_free_table in
  let cons = 
"\tPUSH(FPARG(3)); //  Cdr
\tPUSH(FPARG(2)); // Car
\tCALL(MAKE_SOB_PAIR);
\tDROP(IMM(2));\n" in
  let cons = jump_to_cont ^ (callsWrapper cons) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_cons") in
  let cons = cons ^ "\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);// Moves closure to varfree table. address of cons is: " ^ addr_in_var_free_table in
 opcomnt ^ cons ^ clcomnt;;
(* ---------------------------------- cons ------------------------------ *)
(* ++++++++++++++++++++++++++++++++++ car ++++++++++++++++++++++++++++++ *)
let rts_car var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ car ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ car ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_car:" in
  let addr_in_var_free_table = find_func_addrs "car" var_free_table in
  let car = "\tMOV(R0, INDD(FPARG(2),1));\n" in (* "\tCALL(RTS_CAR);\n" *)
  let car = jump_to_cont ^ (callsWrapper car) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_car") in
  let car = car ^ "\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);//address of car is: " ^ addr_in_var_free_table in   
  opcomnt ^ car ^ clcomnt;;
(* ---------------------------------- car ------------------------------ *)
(* ++++++++++++++++++++++++++++++++++ cdr ++++++++++++++++++++++++++++++ *)
let rts_cdr var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ cdr ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ cdr ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_cdr:" in
  let addr_in_var_free_table = find_func_addrs "cdr" var_free_table in
  let cdr = "\tMOV(R0, INDD(FPARG(2),2));\n" in (* "\tCALL(RTS_CDR);\n" *)
  let cdr = jump_to_cont ^ (callsWrapper cdr) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_cdr") in
  let cdr = cdr ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);//address of cdr is: " ^ addr_in_var_free_table in
  opcomnt ^ cdr ^ clcomnt;;
(* ---------------------------------- cdr ------------------------------ *)
(*++++++++++++++++++++++++++++++++ boolean? ++++++++++++++++++++++++++++ *)
let rts_isBoolean var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ boolean? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ boolean? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isBoolean:" in
  let addr_in_var_free_table = find_func_addrs "boolean?" var_free_table in
  let isBool = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_BOOL));\n\tJUMP_NE(L_bool_ne);\n\tMOV(R0,IMM(1002));\n" in (* "\tCALL(RTS_CDR);\n" *)
  let bool_ne =
"L_bool_ne:
    MOV(R0,IMM(1004));
    POP(FP);
    RETURN;\n\n" in
  let isBool = jump_to_cont ^ (callsWrapper isBool) ^ "\n" ^ bool_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isBoolean") in
  let isBool = isBool ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);//address of boolean? is: " ^ addr_in_var_free_table ^ " adr of true: " ^ addr_true ^ " adr of false: " ^ addr_false in
  opcomnt ^ isBool ^ clcomnt;;
(*-------------------------------- boolean? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ null? ++++++++++++++++++++++++++++ *)
let rts_isNull var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ null? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ null? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isNull:" in
  let addr_in_var_free_table = find_func_addrs "null?" var_free_table in
  let isNil = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_NIL));\n\tJUMP_NE(L_nil_ne);\n\tMOV(R0,IMM(1002));\n" in 
  let null_ne =
"L_nil_ne:
    MOV(R0,IMM(1004));
    POP(FP);
    RETURN;\n\n" in
  let isNil = jump_to_cont ^ (callsWrapper isNil) ^ "\n" ^ null_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isNull") in
  let isNil = isNil ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isNil ^ clcomnt;;
(*-------------------------------- null? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ pair? ++++++++++++++++++++++++++++ *)
let rts_isPair var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ pair? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ pair? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isPair:" in
  let addr_in_var_free_table = find_func_addrs "pair?" var_free_table in
  let isPair = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_PAIR));\n\tJUMP_NE(L_pair_ne);\n\tMOV(R0,IMM(1002));\n" in 
  let pair_ne =
"L_pair_ne:
    MOV(R0,IMM(1004));
    POP(FP);
    RETURN;\n\n" in
  let isPair = jump_to_cont ^ (callsWrapper isPair) ^ "\n" ^ pair_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isPair") in
  let isPair = isPair ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isPair ^ clcomnt;;
(*-------------------------------- pair? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ number? ++++++++++++++++++++++++++++ *)
(* TODO - implement 'write fraction' *)
let rts_isNumber var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ number? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ number? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isNumber:" in
  let addr_in_var_free_table = find_func_addrs "number?" var_free_table in
  let isNumber = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_INTEGER));\n\tJUMP_EQ(L_number_eq);\n\tCMP(R0,IMM(T_FRACTION));\n\tJUMP_EQ(L_number_eq);\n\tMOV(R0,IMM(1004));\n" in 
  let number_eq =
"L_number_eq:
    MOV(R0,IMM(1002));
    POP(FP);
    RETURN;\n\n" in
  let isNumber = jump_to_cont ^ (callsWrapper isNumber) ^ "\n" ^ number_eq ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isNumber") in
  let isNumber = isNumber ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isNumber ^ clcomnt;; 
(*-------------------------------- number? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ rational? ++++++++++++++++++++++++++++ *)
(* TODO - implement 'write fraction' *)
let rts_isRational var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ rational? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ rational? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isRational:" in
  let addr_in_var_free_table = find_func_addrs "rational?" var_free_table in
  let isRational= "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_INTEGER));\n\tJUMP_EQ(L_rational_eq);\n\tCMP(R0,IMM(T_FRACTION));\n\tJUMP_EQ(L_rational_eq);\n\tMOV(R0,IMM(1004));\n" in 
  let rational_eq =
"L_rational_eq:
    MOV(R0,IMM(1002));
    POP(FP);
    RETURN;\n\n" in
  let isRational = jump_to_cont ^ (callsWrapper isRational) ^ "\n" ^ rational_eq ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isRational") in
  let isRational = isRational ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isRational ^ clcomnt;; 
(*-------------------------------- rational? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ vector? ++++++++++++++++++++++++++++ *)
let rts_isVector var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ vector? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ vector? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isVector:" in
  let addr_in_var_free_table = find_func_addrs "vector?" var_free_table in
  let isVector = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_VECTOR));\n\tJUMP_NE(L_vector_ne);\n\tMOV(R0,IMM(1002));\n" in 
  let vector_ne =
"L_vector_ne:
    MOV(R0,IMM(1004));
    POP(FP);
    RETURN;\n\n" in
  let isVector = jump_to_cont ^ (callsWrapper isVector) ^ "\n" ^ vector_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isVector") in
  let isVector = isVector ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isVector ^ clcomnt;;
(*-------------------------------- vector? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ symbol? ++++++++++++++++++++++++++++ *)
let rts_isSymbol var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ symbol? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ symbol? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isSymbol:" in
  let addr_in_var_free_table = find_func_addrs "symbol?" var_free_table in
  let isSymbol = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_SYMBOL));\n\tJUMP_NE(L_symbol_ne);\n\tMOV(R0,IMM(1002));\n" in 
  let symbol_ne =
"L_symbol_ne:
    MOV(R0,IMM(1004));
    POP(FP);
    RETURN;\n\n" in
  let isSymbol = jump_to_cont ^ (callsWrapper isSymbol) ^ "\n" ^ symbol_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isSymbol") in
  let isSymbol = isSymbol ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isSymbol ^ clcomnt;;
(*-------------------------------- symbol? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ procedure? ++++++++++++++++++++++++++++ *)
let rts_isProcedure var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ procedure? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ procedure? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isProcedure:" in
  let addr_in_var_free_table = find_func_addrs "procedure?" var_free_table in
  let isProcedure = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_CLOSURE));\n\tJUMP_NE(L_procedure_ne);\n\tMOV(R0,IMM(1002));\n" in (* TODO WTF is procedure? what do i compare it to? T_CLOSURE?*)
  let procdure_ne =
"L_procedure_ne:
    MOV(R0,IMM(1004));
    POP(FP);
    RETURN;\n\n" in
  let isProcedure = jump_to_cont ^ (callsWrapper isProcedure) ^ "\n" ^ procdure_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isProcedure") in
  let isProcedure = isProcedure ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isProcedure ^ clcomnt;;
(*-------------------------------- procedure? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ string? ++++++++++++++++++++++++++++ *)
let rts_isString var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ string? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ string? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isString:" in
  let addr_in_var_free_table = find_func_addrs "string?" var_free_table in
  let isString = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_STRING));\n\tJUMP_NE(L_string_ne);\n\tMOV(R0,IMM(1002));\n" in 
  let string_ne =
"L_string_ne:
    MOV(R0,IMM(1004));
    POP(FP);
    RETURN;\n\n" in
  let isString = jump_to_cont ^ (callsWrapper isString) ^ "\n" ^ string_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isString") in
  let isString = isString ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isString ^ clcomnt;;
(*-------------------------------- string? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ char? ++++++++++++++++++++++++++++ *)
let rts_isChar var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ char? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ char? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isChar:" in
  let addr_in_var_free_table = find_func_addrs "char?" var_free_table in
  let isChar = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_CHAR));\n\tJUMP_NE(L_char_ne);\n\tMOV(R0,IMM(1002));\n" in 
  let char_ne =
"L_char_ne:
    MOV(R0,IMM(1004));
    POP(FP);
    RETURN;\n\n" in
  let isChar = jump_to_cont ^ (callsWrapper isChar) ^ "\n" ^ char_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isChar") in
  let isChar = isChar ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isChar ^ clcomnt;;
(*-------------------------------- char? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ integer? ++++++++++++++++++++++++++++ *)
let rts_isInteger var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ integer? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ integer? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isInteger:" in
  let addr_in_var_free_table = find_func_addrs "integer?" var_free_table in
  let isInteger = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_INTEGER));\n\tJUMP_NE(L_integer_ne);\n\tMOV(R0,IMM(1002));\n" in 
  let integer_ne =
"L_integer_ne:
    MOV(R0,IMM(1004));
    POP(FP);
    RETURN;\n\n" in
  let isInteger = jump_to_cont ^ (callsWrapper isInteger) ^ "\n" ^ integer_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isInteger") in
  let isInteger = isInteger ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isInteger ^ clcomnt;;
(*-------------------------------- integer? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ zero? ++++++++++++++++++++++++++++ *)
let rts_isZero var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ zero? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ zero? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_isZero:" in
  let addr_in_var_free_table = find_func_addrs "zero?" var_free_table in
  let isZero = "\tMOV(R0, IND(FPARG(2)));\n\tCMP(R0,IMM(T_INTEGER));\n\tJUMP_NE(L_zero_ne);\n\tMOV(R0, INDD(FPARG(2),1));\n\tCMP(R0,IMM(0));\n\tJUMP_NE(L_zero_ne);\n\tMOV(R0,IMM(1002));\n" in 
  let zero_ne =
"L_zero_ne:
    MOV(R0,IMM(1004));
    POP(FP);
    RETURN;\n\n" in
  let isZero = jump_to_cont ^ (callsWrapper isZero) ^ "\n" ^ zero_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_isZero") in
  let isZero = isZero ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isZero ^ clcomnt;;
(*-------------------------------- zero? ---------------------------- *)


(*++++++++++++++++++++++++++++++++ set-car! ++++++++++++++++++++++++++++ *)
let rts_set_car_bang var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ set-car! ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ set-car! ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_set_car:" in
  let addr_in_var_free_table = find_func_addrs "set-car!" var_free_table in
  let set_car = "\tMOV(R0,FPARG(3));\n\tMOV(R1,FPARG(2));\n\tMOV(INDD(R1,1),R0);\n\tMOV(R0," ^ addr_void ^");\n" in 
  let set_car = jump_to_cont ^ (callsWrapper set_car) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_set_car") in
  let set_car = set_car ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ set_car ^ clcomnt;;
(*-------------------------------- set-car! ---------------------------- *)
(*++++++++++++++++++++++++++++++++ set-cdr! ++++++++++++++++++++++++++++ *)
let rts_set_cdr_bang var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ set-cdr! ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ set-cdr! ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_set_cdr:" in
  let addr_in_var_free_table = find_func_addrs "set-cdr!" var_free_table in
  let set_cdr = "\tMOV(R0,FPARG(3));\n\tMOV(R1,FPARG(2));\n\tMOV(INDD(R1,2),R0);\n\tMOV(R0," ^ addr_void ^");\n" in 
  let set_cdr = jump_to_cont ^ (callsWrapper set_cdr) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_set_cdr") in
  let set_cdr = set_cdr ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ set_cdr ^ clcomnt;;
(*-------------------------------- set-cdr! ---------------------------- *)
(*++++++++++++++++++++++++++++++++ not ++++++++++++++++++++++++++++ *)
let rts_not var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ not ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ not ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_not:" in
  let addr_in_var_free_table = find_func_addrs "not" var_free_table in
  let not_str = "\tMOV(R0,FPARG(2));\n\tCMP(R0,IMM(1004));\n\tJUMP_EQ(L_not_ne);\n\tMOV(R0,IMM(1004));\n" in 
  let not_ne =
"L_not_ne:
    MOV(R0,IMM(1002));
    POP(FP);
    RETURN;\n\n" in
  let not_str = jump_to_cont ^ (callsWrapper not_str) ^ "\n" ^ not_ne ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_not") in
  let not_str = not_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ not_str ^ clcomnt;;
(*-------------------------------- not ---------------------------- *)
(*++++++++++++++++++++++++++++++++ char->integer ++++++++++++++++++++++++++++ *)
let rts_char_to_integer var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ char->integer ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ char->integer ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_char_to_int:" in
  let addr_in_var_free_table = find_func_addrs "char->integer" var_free_table in
  let ch_to_int = "\tMOV(R0,INDD(FPARG(2),1));\n\tPUSH(R0);\n\tCALL(MAKE_SOB_INTEGER);\n\tDROP(1);\n" in 
  let ch_to_int = jump_to_cont ^ (callsWrapper ch_to_int) ^ "\n"  ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_char_to_int") in
  let ch_to_int = ch_to_int ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ ch_to_int ^ clcomnt;;
(*-------------------------------- char->integer ---------------------------- *)
(*++++++++++++++++++++++++++++++++ string-length ++++++++++++++++++++++++++++ *)
let rts_string_length var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ string-length ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ string-length ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_string_length:" in
  let addr_in_var_free_table = find_func_addrs "string-length" var_free_table in
  let string_length = "\tMOV(R0,INDD(FPARG(2),1));\n\tPUSH(R0);\n\tCALL(MAKE_SOB_INTEGER);\n\tDROP(1);\n" in 
  let string_length = jump_to_cont ^ (callsWrapper string_length) ^ "\n"  ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_string_length") in
  let string_length = string_length ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ string_length ^ clcomnt;;
(*-------------------------------- string-length ---------------------------- *)
(*++++++++++++++++++++++++++++++++ vector-length ++++++++++++++++++++++++++++ *)
let rts_vector_length var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ vector-length ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ vector-length ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_vector_length:" in
  let addr_in_var_free_table = find_func_addrs "vector-length" var_free_table in
  let vector_length = "\tMOV(R0,INDD(FPARG(2),1));\n\tPUSH(R0);\n\tCALL(MAKE_SOB_INTEGER);\n\tDROP(1);\n" in 
  let vector_length = jump_to_cont ^ (callsWrapper vector_length) ^ "\n"  ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_vector_length") in
  let vector_length = vector_length ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ vector_length ^ clcomnt;;
(*-------------------------------- vector-length ---------------------------- *)
(*++++++++++++++++++++++++++++++++ integer->char ++++++++++++++++++++++++++++ *)
let rts_integer_to_char var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ integer->char ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ integer->char ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_integer_to_char:" in
  let addr_in_var_free_table = find_func_addrs "integer->char" var_free_table in
  let int_to_char_str = "\tMOV(R0,INDD(FPARG(2),1));\n\tPUSH(R0);\n\tCALL(MAKE_SOB_CHAR);\n\tDROP(1);\n" in 
  let int_to_char_str = jump_to_cont ^ (callsWrapper int_to_char_str) ^ "\n"  ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_integer_to_char") in
  let int_to_char_str = int_to_char_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ int_to_char_str ^ clcomnt;;
(*-------------------------------- integer->char ---------------------------- *)
(*++++++++++++++++++++++++++++++++ denominator ++++++++++++++++++++++++++++ *)
let rts_denominator var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ denominator ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ denominator ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_denominator:" in
  let addr_in_var_free_table = find_func_addrs "denominator" var_free_table in
  let denom_str = "\tMOV(R0,IND(FPARG(2)));\n\tCMP(R0,T_INTEGER);\n\tJUMP_EQ(L_de_integer_eq);\n\tMOV(R0,INDD(FPARG(2),2));\n\tPUSH(R0);\n\tCALL(MAKE_SOB_INTEGER);\n\tDROP(1);\n" in 
  let integer_eq ="
L_de_integer_eq:
    MOV(R0,IMM(1));
    PUSH(R0);
    CALL(MAKE_SOB_INTEGER);
    DROP(1);
    POP(FP);
    RETURN;\n\n" in
  let denom_str = jump_to_cont ^ (callsWrapper denom_str) ^ "\n"  ^ integer_eq ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_denominator") in
  let denom_str = denom_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ denom_str ^ clcomnt;;
(*-------------------------------- numerator ---------------------------- *)
(*++++++++++++++++++++++++++++++++ numerator ++++++++++++++++++++++++++++ *)
let rts_numerator var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ numerator ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ numerator ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_numerator:" in
  let addr_in_var_free_table = find_func_addrs "numerator" var_free_table in
  let num_str = "\tMOV(R0,(FPARG(2)));\n\tCMP(IND(R0),T_INTEGER);\n\tJUMP_EQ(L_num_integer_eq);\n\tMOV(R0,INDD(FPARG(2),1));\n\tPUSH(R0);\n\tCALL(MAKE_SOB_INTEGER);\n\tDROP(1);\n" in 
  let integer_eq ="
L_num_integer_eq:
    MOV(R0,INDD(R0,1));
    PUSH(R0);
    CALL(MAKE_SOB_INTEGER);
    DROP(1);
    POP(FP);
    RETURN;\n\n" in
  let num_str = jump_to_cont ^ (callsWrapper num_str) ^ "\n"  ^ integer_eq ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_numerator") in
  let num_str = num_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ num_str ^ clcomnt;;
(*-------------------------------- numerator ---------------------------- *)
(*++++++++++++++++++++++++++++++++ remainder ++++++++++++++++++++++++++++ *)
let rts_remainder var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ remainder ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ remainder ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_remainder:" in
  let addr_in_var_free_table = find_func_addrs "remainder" var_free_table in
  let rem_str = "\tMOV(R0,INDD(FPARG(2),1));\n\tREM(R0,INDD(FPARG(3),1));\n\tPUSH(R0);\n\tCALL(MAKE_SOB_INTEGER);\n\tDROP(1);\n" in 
  let rem_str = jump_to_cont ^ (callsWrapper rem_str) ^ "\n"   ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_remainder") in
  let rem_str = rem_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ rem_str ^ clcomnt;;
(*-------------------------------- remainder ---------------------------- *)
(*++++++++++++++++++++++++++++++++ make-string ++++++++++++++++++++++++++++ *)
let rts_make_string var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ make-string ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ make-string ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_make_string:" in
  let addr_in_var_free_table = find_func_addrs "make-string" var_free_table in
  let make_string_str = 
"    MOV(R0,INDD(FPARG(2),1)); // RO = n
    CMP(R0,IMM(0));
    JUMP_LE(L_make_string_num_neg);
    MOV(R1,IMM(0)); // int i = 0
L_make_string_loop:
    CMP(R1,R0);
    JUMP_GE(L_end_make_string_loop);
    PUSH(INDD(FPARG(3),1));
    INCR(R1);
    JUMP(L_make_string_loop);

L_end_make_string_loop:
    PUSH(R0);
    ADD(R1,IMM(1));
    CALL(MAKE_SOB_STRING);
    DROP(R1);
    POP(FP);
    RETURN;

L_make_string_num_neg:
    MOV(R0,IMM(1));
    PUSH(IMM(0));
    CALL(MAKE_SOB_STRING);
    DROP(1);\n" in
  let make_string_str = jump_to_cont ^ (callsWrapper make_string_str) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_make_string") in
  let make_string_str = make_string_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ make_string_str ^ clcomnt;;
(*-------------------------------- make-string ---------------------------- *)
(*++++++++++++++++++++++++++++++++ make-vector ++++++++++++++++++++++++++++ *)
let rts_make_vector var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ make-vector ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ make-vector ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_make_vector:" in
  let addr_in_var_free_table = find_func_addrs "make-vector" var_free_table in
  let make_vector_str = 
"    PUSH(IMM(0));
    CALL(MAKE_SOB_INTEGER);
    DROP(1);
    MOV(R2,INDD(FPARG(2),1)); // RO = n
    CMP(R2,IMM(0)); // if n == 0 creates empty vector #()
    JUMP_LE(L_make_vector_num_neg);
    MOV(R1,IMM(0)); // int i = 0
L_make_vector_loop:
    CMP(R1,R2);
    JUMP_GE(L_end_make_vector_loop);
    CMP(FPARG(1),IMM(1)); // if got only one function argument --> push zeroes.
    JUMP_EQ(L_make_vector_of_zeroes)
    PUSH(FPARG(3));
    INCR(R1);
    JUMP(L_make_vector_loop);


L_make_vector_of_zeroes:
    PUSH(R0);
    INCR(R1);
    JUMP(L_make_vector_loop);

L_end_make_vector_loop:
    PUSH(R2);
    MOV(R1,R2);
    ADD(R1,IMM(1));
    CALL(MAKE_SOB_VECTOR);
    DROP(R1);
    POP(FP);
    RETURN;


L_make_vector_num_neg:
    MOV(R0,IMM(1));
    PUSH(IMM(0));
    CALL(MAKE_SOB_VECTOR);
    DROP(1);\n" in
  let make_vector_str = jump_to_cont ^ (callsWrapper make_vector_str) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_make_vector") in
  let make_vector_str = make_vector_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ make_vector_str ^ clcomnt;;
(*-------------------------------- make-vector ---------------------------- *)
(*++++++++++++++++++++++++++++++++ vector ++++++++++++++++++++++++++++ *)
let rts_vector var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ vector ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ vector ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_vector:" in
  let addr_in_var_free_table = find_func_addrs "vector" var_free_table in
  let vector_str = 
"    MOV(R0,FPARG(1)); // r0  = num of args. 
    MOV(R1,IMM(0));// r1 = 0 (start) . incrementing r1 in loop.
L_vector_start_loop:    
    CMP(R1,R0); // while (r1 < n) do:
    JUMP_GE(L_vector_exit_loop);
    MOV(R2,R1);
    ADD(R2,IMM(2));
    PUSH(FPARG(R2));
    INCR(R1);
    JUMP(L_vector_start_loop);

L_vector_exit_loop:
    PUSH(R0);
    ADD(R1,IMM(1));
    CALL(MAKE_SOB_VECTOR);
    DROP(R1);\n" in
  let vector_str = jump_to_cont ^ (callsWrapper vector_str) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_vector") in
  let vector_str = vector_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ vector_str ^ clcomnt;;
(*-------------------------------- vector ---------------------------- *)
(*++++++++++++++++++++++++++++++++ + ++++++++++++++++++++++++++++ *)
let rts_plus var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ + ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ + ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_plus:" in
  let addr_in_var_free_table = find_func_addrs "+" var_free_table in
  let (loop_code_label, loop_end_label) = make_loop_labels() in
  let plus =  (*TODO CHANGE ALL THE +,-,*,/,... to create a new fraction for every iteration*)
"\tCMP(IMM(0), FPARG(1));
\tJUMP_NE(L_prim_plus_with_params);
\tMOV(R1, 1);
\tMOV(R2, 1);
\tJUMP(" ^ loop_end_label ^ ");
L_prim_plus_with_params:
\tMOV(R0, 1);
\tCMP(IND(FPARG(2)), T_FRACTION);
\tJUMP_NE(L_prim_plus_not_fraction);
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, INDD(FPARG(2), 2));
\tJUMP(" ^ loop_code_label ^ ");
L_prim_plus_not_fraction:
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, 1);
" ^ loop_code_label ^ ":
\tCMP(R0, FPARG(1));
\tJUMP_GE(" ^ loop_end_label ^ ");
\t\tMOV(R3, R0);
\t\tADD(R3, 2);
\t\tCMP(IND(FPARG(R3)), T_FRACTION);
\t\tJUMP_NE(L_prim_plus_loop_not_fraction_start);
\t\tMUL(R1, INDD(FPARG(R3), 2));
\t\tMUL(R2, INDD(FPARG(R3), 1));
\t\tADD(R1, R2);
\t\tDIV(R2, INDD(FPARG(R3), 1));
\t\tMUL(R2, INDD(FPARG(R3), 2));
\t\tJUMP(L_prim_plus_loop_not_fraction_end);
L_prim_plus_loop_not_fraction_start:
\t\tMOV(R4,R2);
\t\tMUL(R4, INDD(FPARG(R3), 1));
\t\tADD(R1, R4);
L_prim_plus_loop_not_fraction_end:
\t\tADD(R0, 1);
\t\tJUMP(" ^ loop_code_label ^ ");
" ^ loop_end_label ^ ":
\tPUSH(R2);
\tPUSH(R1);
\tCALL(MAKE_SOB_FRACTION);
\tDROP(2);\n" in 
  let plus = jump_to_cont ^ (callsWrapper plus) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_plus") in
  let plus = plus ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ plus ^ clcomnt;;
(*-------------------------------- + ---------------------------- *)
(*++++++++++++++++++++++++++++++++ - ++++++++++++++++++++++++++++ *)
let rts_minus var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ - ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ - ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_minus:" in
  let addr_in_var_free_table = find_func_addrs "-" var_free_table in
  let (loop_code_label, loop_end_label) = make_loop_labels() in
  let minus = (*TODO: PUT CMP TO CHECK IF NUM OF PARAMS IS 0. *)
"\tMOV(R0, 1);
\tCMP(FPARG(1), 1);
\tJUMP_NE(L_prim_minus_lot_params);
\tCMP(IND(FPARG(2)), T_FRACTION);
\tJUMP_NE(L_prim_minus_one_param_not_fraction);
\tMOV(R1, INDD(FPARG(2), 1));
\tMUL(R1, -1);
\tMOV(R2, INDD(FPARG(2), 2));
JUMP(" ^ loop_end_label ^ ");
L_prim_minus_one_param_not_fraction:
\tMOV(R1, INDD(FPARG(2), 1));
\tMUL(R1, -1);
\tMOV(R2, 1);
JUMP(" ^ loop_end_label ^ ");
L_prim_minus_lot_params:
\tCMP(IND(FPARG(2)), T_FRACTION);
\tJUMP_NE(L_prim_minus_not_fraction);
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, INDD(FPARG(2), 2));
\tJUMP(" ^ loop_code_label ^ ");
L_prim_minus_not_fraction:
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, 1);
" ^ loop_code_label ^ ":
\tCMP(R0, FPARG(1));
\tJUMP_GE(" ^ loop_end_label ^ ");
\t\tMOV(R3, R0);
\t\tADD(R3, 2);
\t\tCMP(IND(FPARG(R3)), T_FRACTION);
\t\tJUMP_NE(L_prim_minus_loop_not_fraction_start);
\t\tMUL(R1, INDD(FPARG(R3), 2));
\t\tMUL(R2, INDD(FPARG(R3), 1));
\t\tSUB(R1, R2);
\t\tDIV(R2, INDD(FPARG(R3), 1));
\t\tMUL(R2, INDD(FPARG(R3), 2));
\t\tJUMP(L_prim_minus_loop_not_fraction_end);
L_prim_minus_loop_not_fraction_start:
\t\tMOV(R4,R2);
\t\tMUL(R4, INDD(FPARG(R3), 1));
\t\tSUB(R1, R4);
L_prim_minus_loop_not_fraction_end:
\t\tADD(R0, 1);
\t\tJUMP(" ^ loop_code_label ^ ");
" ^ loop_end_label ^ ":
\tPUSH(R2);
\tPUSH(R1);
\tCALL(MAKE_SOB_FRACTION);
\tDROP(2);\n" in 
  let minus = jump_to_cont ^ (callsWrapper minus) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_minus") in
  let minus = minus ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "), R0);" in
  opcomnt ^ minus ^ clcomnt;;
(*-------------------------------- - ---------------------------- *)
(*++++++++++++++++++++++++++++++++ * ++++++++++++++++++++++++++++ *)
let rts_mul var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ * ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ * ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_mul:" in
  let addr_in_var_free_table = find_func_addrs "*" var_free_table in
  let (loop_code_label, loop_end_label) = make_loop_labels() in
  let mul = (*TODO: PUT CMP TO CHECK IF NUM OF PARAMS IS 0. *)
"\tMOV(R0, 0); 
\tMOV(R1, 1);
\tMOV(R2, 1);
" ^ loop_code_label ^ ":
\tCMP(R0, FPARG(1));
\tJUMP_GE(" ^ loop_end_label ^ ");
\t\tMOV(R3, R0);
\t\tADD(R3, 2);
\t\tCMP(IND(FPARG(R3)), T_FRACTION);
\t\tJUMP_NE(nL_prim_mul_loop_not_fraction_start);
\t\tMUL(R1, INDD(FPARG(R3), 1));
\t\tMUL(R2, INDD(FPARG(R3), 2));
\t\tJUMP(nL_prim_mul_loop_not_fraction_end);
nL_prim_mul_loop_not_fraction_start:
\t\tMUL(R1, INDD(FPARG(R3), 1));
nL_prim_mul_loop_not_fraction_end:
\t\tADD(R0, 1);
\t\tJUMP(" ^ loop_code_label ^ ");
" ^ loop_end_label ^ ":
\tPUSH(R2);
\tPUSH(R1);
\tCALL(MAKE_SOB_FRACTION);
\tDROP(2);\n" in 
  let mul = jump_to_cont ^ (callsWrapper mul) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_mul") in
  let mul = mul ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "), R0);" in
  opcomnt ^ mul ^ clcomnt;;
(*-------------------------------- * ---------------------------- *)
(*++++++++++++++++++++++++++++++++ / ++++++++++++++++++++++++++++ *)
let rts_div var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ / ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ / ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_div:" in
  let addr_in_var_free_table = find_func_addrs "/" var_free_table in
  let (loop_code_label1, loop_end_label1) = make_loop_labels() in
  let (loop_code_label2, loop_end_label2) = make_loop_labels() in
  let div = (*TODO: PUT CMP TO CHECK IF NUM OF PARAMS IS 0. *)

"\tCMP(FPARG(1),1);
\tJUMP_EQ(" ^ loop_code_label2 ^ ");
\tMOV(R0, 1); 
\tCMP(IND(FPARG(2)), T_FRACTION);
\tJUMP_NE(L_prim_div_not_fraction);
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, INDD(FPARG(2), 2));
\tJUMP(" ^ loop_code_label1 ^ ");
L_prim_div_not_fraction:
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, 1);
" ^ loop_code_label1 ^ ":
\tCMP(R0, FPARG(1));
\tJUMP_GE(" ^ loop_end_label1 ^ ");
\t\tMOV(R3, R0);
\t\tADD(R3, 2);
\tCMP(IND(FPARG(R3)), T_FRACTION);
\tJUMP_NE(L_prim_div_loop_not_fraction_start);
\t\tMUL(R1, INDD(FPARG(R3), 2));
\t\tMUL(R2, INDD(FPARG(R3), 1));
\t\tJUMP(L_prim_div_loop_not_fraction_end);
L_prim_div_loop_not_fraction_start:
\t\tMUL(R2, INDD(FPARG(R3), 1));
L_prim_div_loop_not_fraction_end:
\t\tADD(R0, 1);
\t\tJUMP(" ^ loop_code_label1 ^ ");
" ^ loop_end_label1 ^ ":
\tPUSH(R2);
\tPUSH(R1);
\tCALL(MAKE_SOB_FRACTION);
\tDROP(2);
\tJUMP(" ^ loop_end_label2 ^ ");
" ^ loop_code_label2 ^ ":
\tCMP(IND(FPARG(2)), T_FRACTION);
\tJUMP_NE(L_prim_div_not_fraction_special);
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, INDD(FPARG(2), 2));
\tJUMP(L_prim_div_not_fraction_special_end);
L_prim_div_not_fraction_special:
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, 1);
L_prim_div_not_fraction_special_end:
\tPUSH(R1);
\tPUSH(R2);
\tCALL(MAKE_SOB_FRACTION);
\tDROP(2);
" ^ loop_end_label2 ^ ":
\n" in
  let div = jump_to_cont ^ (callsWrapper div) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_div") in
  let div = div ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "), R0);" in
  opcomnt ^ div ^ clcomnt;;
(*-------------------------------- / ---------------------------- *)
(*++++++++++++++++++++++++++++++++ = ++++++++++++++++++++++++++++ *)
let rts_equal var_free_table const_table = 
  let opcomnt = "\n\t/* ++++++++++++ = ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ = ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_equal:" in
  let addr_in_var_free_table = find_func_addrs "=" var_free_table in
  let (loop_code_label, loop_end_label) = make_loop_labels() in
  let equal = (*TODO: PUT CMP TO CHECK IF NUM OF PARAMS IS 0. *)
"\tMOV(R0, 1); 
CMP(IND(FPARG(2)), T_FRACTION);
JUMP_NE(L_prim_equal_not_fraction);
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, INDD(FPARG(2), 2));
\tJUMP(" ^ loop_code_label ^ ");
L_prim_equal_not_fraction:
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, 1);
" ^ loop_code_label ^ ":
\tCMP(R0, FPARG(1));
\tJUMP_GE(" ^ loop_end_label ^ ");
\t\tMOV(R3, R0);
\t\tADD(R3, 2);
\tCMP(IND(FPARG(R3)), T_FRACTION);
\tJUMP_NE(L_prim_equal_loop_not_fraction_start);
\t\tCMP(R1, INDD(FPARG(R3), 1));
\t\tJUMP_NE(L_prim_equal_false);
\t\tCMP(R2, INDD(FPARG(R3), 2));
\t\tJUMP_NE(L_prim_equal_false);
\t\tJUMP(L_prim_equal_loop_not_fraction_end);
L_prim_equal_loop_not_fraction_start:
\t\tCMP(R1, INDD(FPARG(R3), 1));
\t\tJUMP_NE(L_prim_equal_false);
\t\tCMP(R2, 1);
\t\tJUMP_NE(L_prim_equal_false);
L_prim_equal_loop_not_fraction_end:
\t\tADD(R0, 1);
\t\tJUMP(" ^ loop_code_label ^ ");
" ^ loop_end_label ^ ":
\tMOV(R0, " ^ getConstAddress (Bool true) const_table ^");
\tJUMP(L_prim_equal_end);
L_prim_equal_false:
\tMOV(R0, " ^ getConstAddress (Bool false) const_table ^ ");
L_prim_equal_end:" in
  let equal = jump_to_cont ^ (callsWrapper equal) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_equal") in
  let equal = equal ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ equal ^ clcomnt;;
(*-------------------------------- = ---------------------------- *)
(*++++++++++++++++++++++++++++++++ < ++++++++++++++++++++++++++++ *)
let rts_less_then var_free_table const_table = 
  let opcomnt = "\n\t/* ++++++++++++ < ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ < ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_less_then:" in
  let addr_in_var_free_table = find_func_addrs "<" var_free_table in
  let (loop_code_label, loop_end_label) = make_loop_labels() in
  let less_then = (*TODO: PUT CMP TO CHECK IF NUM OF PARAMS IS 0. *)
"\tMOV(R0, 1); 
\tCMP(IND(FPARG(2)), T_FRACTION);
\tJUMP_NE(L_prim_less_then_not_fraction);
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, INDD(FPARG(2), 2));
\tJUMP(" ^ loop_code_label ^ ");
L_prim_less_then_not_fraction:
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, 1);
" ^ loop_code_label ^ ":
\tCMP(R0, FPARG(1));
\tJUMP_GE(" ^ loop_end_label ^ ");
\t\tMOV(R3, R0);
\t\tADD(R3, 2);
\tCMP(IND(FPARG(R3)), T_FRACTION);
\tJUMP_NE(L_prim_less_then_loop_not_fraction_start);
\t\tMOV(R4, INDD(FPARG(R3), 1));
\t\tMUL(R4, R2);
\t\tMOV(R5, INDD(FPARG(R3), 2));
\t\tMUL(R5, R1);
\t\tCMP(R5, R4);
\t\tJUMP_GE(L_prim_less_then_false);
\t\tMOV(R1, INDD(FPARG(R3), 1));
\t\tMOV(R2, INDD(FPARG(R3), 2));
\t\tJUMP(L_prim_less_then_loop_not_fraction_end);
L_prim_less_then_loop_not_fraction_start:
\t\tMOV(R4, INDD(FPARG(R3),1));
\t\tMUL(R4, R2);
\t\tCMP(R1, R4);
\t\tJUMP_GE(L_prim_less_then_false);
\t\tMOV(R1, R4);
L_prim_less_then_loop_not_fraction_end:
\t\tADD(R0, 1);
\t\tJUMP(" ^ loop_code_label ^ ");
" ^ loop_end_label ^ ":
\tMOV(R0, " ^ getConstAddress (Bool true) const_table ^");
\tJUMP(L_prim_less_then_end);
L_prim_less_then_false:
\tMOV(R0, " ^ getConstAddress (Bool false) const_table ^ ");
L_prim_less_then_end:" in
  let less_then = jump_to_cont ^ (callsWrapper less_then) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_less_then") in
  let less_then = less_then ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ less_then ^ clcomnt;;
(*-------------------------------- < ---------------------------- *)
(*++++++++++++++++++++++++++++++++ > ++++++++++++++++++++++++++++ *)
let rts_greater_then var_free_table const_table = 
  let opcomnt = "\n\t/* ++++++++++++ > ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ > ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_greater_then:" in
  let addr_in_var_free_table = find_func_addrs ">" var_free_table in
  let (loop_code_label, loop_end_label) = make_loop_labels() in
  let greater_then = (*TODO: PUT CMP TO CHECK IF NUM OF PARAMS IS 0. *)
"\tMOV(R0, 1); 
CMP(IND(FPARG(2)), T_FRACTION);
JUMP_NE(L_prim_greater_then_not_fraction);
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, INDD(FPARG(2), 2));
\tJUMP(" ^ loop_code_label ^ ");
L_prim_greater_then_not_fraction:
\tMOV(R1, INDD(FPARG(2), 1));
\tMOV(R2, 1);
" ^ loop_code_label ^ ":
\tCMP(R0, FPARG(1));
\tJUMP_GE(" ^ loop_end_label ^ ");
\t\tMOV(R3, R0);
\t\tADD(R3, 2);
\tCMP(IND(FPARG(R3)), T_FRACTION);
\tJUMP_NE(L_prim_greater_then_loop_not_fraction_start);
\t\tMOV(R4, INDD(FPARG(R3), 1));
\t\tMUL(R4, R2);
\t\tMOV(R5, INDD(FPARG(R3), 2));
\t\tMUL(R5, R1);
\t\tCMP(R5, R4);
\t\tJUMP_LE(L_prim_greater_then_false);
\t\tMOV(R1, INDD(FPARG(R3), 1));
\t\tMOV(R2, INDD(FPARG(R3), 2));
\t\tJUMP(L_prim_greater_then_loop_not_fraction_end);
L_prim_greater_then_loop_not_fraction_start:
\t\tMOV(R4, INDD(FPARG(R3),1));
\t\tMUL(R4, R2);
\t\tCMP(R1, R4);
\t\tJUMP_LE(L_prim_greater_then_false);
\t\tMOV(R1, R4);
L_prim_greater_then_loop_not_fraction_end:
\t\tADD(R0, 1);
\t\tJUMP(" ^ loop_code_label ^ ");
" ^ loop_end_label ^ ":
\tMOV(R0, " ^ getConstAddress (Bool true) const_table ^");
\tJUMP(L_prim_greater_then_end);
L_prim_greater_then_false:
\tMOV(R0, " ^ getConstAddress (Bool false) const_table ^ ");
L_prim_greater_then_end:" in
  let greater_then = jump_to_cont ^ (callsWrapper greater_then) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_greater_then") in
  let greater_then = greater_then ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ greater_then ^ clcomnt;;
(*-------------------------------- > ---------------------------- *)
(*++++++++++++++++++++++++++++++++ string-ref ++++++++++++++++++++++++++++ *)
(* TODO. IF HAVE TIME CHANGE R0+2 to MOV(R3,R2), ADD(R3,2)....*)
let rts_string_ref var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ string-ref ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ string-ref ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_string_ref:" in
  let addr_in_var_free_table = find_func_addrs "string-ref" var_free_table in
  let string_ref_str = 
"    MOV(R0,INDD(FPARG(3),1)); // r0  = char at n. 
    MOV(R1,INDD(FPARG(2),1)); // r1 = length of string
    CMP(R0,R1); // if (char at n) >= length of string then exit.
    JUMP_GE(L_string_ref_exit);
    CMP(R0,IMM(0)); // if (char at n) < 0 then exit.
    JUMP_LT(L_string_ref_exit);
    CMP(R0,IMM(0)); // if (char at n) == 0 then exit.
    JUMP_EQ(L_string_ref_goto_zero);
    MOV(R1,IMM(0));

L_string_ref_start_loop:
    CMP(R1,R0);
    JUMP_GE(L_string_ref_exit_loop);
    PUSH(INDD(FPARG(2),R1+2));
    INCR(R1);
    JUMP(L_string_ref_start_loop);

L_string_ref_exit_loop:
    PUSH(INDD(FPARG(2),R1+2));
    INCR(R1);
    CALL(MAKE_SOB_CHAR);
    DROP(R1);
    POP(FP);
    RETURN;

L_string_ref_goto_zero:
    PUSH(INDD(FPARG(2),2));
    //PUSH(1);
    CALL(MAKE_SOB_CHAR);
    DROP(1);
    POP(FP);
    RETURN;

L_string_ref_exit:
    //TODO  not sure if need to do MOV(R0,IMM(1));
    PUSH(IMM(0));
    CALL(MAKE_SOB_CHAR);
    DROP(1);\n" in
  let string_ref_str = jump_to_cont ^ (callsWrapper string_ref_str) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_string_ref") in
  let string_ref_str = string_ref_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ string_ref_str ^ clcomnt;;
(*-------------------------------- string-ref ---------------------------- *)
(*++++++++++++++++++++++++++++++++ vector-ref ++++++++++++++++++++++++++++ *)
(* TODO. IF HAVE TIME CHANGE R0+2 to MOV(R3,R2), ADD(R3,2)....*)
let rts_vector_ref var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ vector-ref ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ vector-ref ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_vector_ref:" in
  let addr_in_var_free_table = find_func_addrs "vector-ref" var_free_table in
  let vector_ref_str = 
"    MOV(R0,INDD(FPARG(3),1)); // r0  = char at n. 
    MOV(R1,INDD(FPARG(2),1)); // r1 = length of vector
    CMP(R0,R1); // if (char at n) >= length of vector then exit.
    JUMP_GE(L_vector_ref_exit);
    CMP(R0,IMM(0)); // if (char at n) < 0 then exit.
    JUMP_LT(L_vector_ref_exit);
    CMP(R0,IMM(0)); // if (char at n) == 0 then exit.
    JUMP_EQ(L_vector_ref_goto_zero);
    MOV(R1,IMM(0));

L_vector_ref_start_loop:
    CMP(R1,R0);
    JUMP_GE(L_vector_ref_exit_loop);
    PUSH(INDD(FPARG(2),R1+2));
    INCR(R1);
    JUMP(L_vector_ref_start_loop);

L_vector_ref_exit_loop:
    MOV(R0,INDD(FPARG(2),R1+2));
    DROP(R1);
    POP(FP);
    RETURN;

L_vector_ref_goto_zero:
    MOV(R0,INDD(FPARG(2),2));
    POP(FP);
    RETURN;

L_vector_ref_exit:
    //enteres here only in case n < 0. which will never happend.\n" in
  let vector_ref_str = jump_to_cont ^ (callsWrapper vector_ref_str) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_vector_ref") in
  let vector_ref_str = vector_ref_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ vector_ref_str ^ clcomnt;;
(*-------------------------------- vector-ref ---------------------------- *)
(*++++++++++++++++++++++++++++++++ string-set! ++++++++++++++++++++++++++++ *)
let rts_string_set_bang var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ string-set! ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ string-set! ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_rts_string_set_bang:" in
  let addr_in_var_free_table = find_func_addrs "string-set!" var_free_table in
  let rts_string_set_bang_str = 
"   // check if index is larger then string length or smaller then 0
    MOV(R0,IMM(0)); // R0 = 0
    MOV(R1,INDD(FPARG(3),1)); // index of char to be changed
    MOV(R2,INDD(FPARG(2),1)); // LENGTH OF STRING
    CMP(R1,R0);
    JUMP_LT(L_exit_string_set_bang);
    CMP(R1,R2);
    JUMP_GE(L_exit_string_set_bang);
    MOV(R0,FPARG(2)); // pointer to string
    ADD(R1,IMM(2));
    MOV(R2,INDD(FPARG(4),1)); //  char to be put instead of previous char
    MOV(INDD(R0,R1),R2);
    MOV(R0," ^ addr_void ^ ");
    POP(FP);
    RETURN;

L_exit_string_set_bang:
MOV(R0," ^ addr_void ^ ");\n" in
  let rts_string_set_bang_str = jump_to_cont ^ (callsWrapper rts_string_set_bang_str) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_rts_string_set_bang") in
  let rts_string_set_bang_str = rts_string_set_bang_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ rts_string_set_bang_str ^ clcomnt;;
(*-------------------------------- string-set! ---------------------------- *)
(*++++++++++++++++++++++++++++++++ vector-set! ++++++++++++++++++++++++++++ *)
let rts_vector_set_bang var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ vector-set! ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ vector-set! ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_rts_vector_set_bang:" in
  let addr_in_var_free_table = find_func_addrs "vector-set!" var_free_table in
  let rts_vector_set_bang_str = 
"   // check if index is larger then vector length or smaller then 0
    MOV(R0,IMM(0)); // R0 = 0
    MOV(R1,INDD(FPARG(3),1)); // index of char to be changed
    MOV(R2,INDD(FPARG(2),1)); // LENGTH OF STRING
    CMP(R1,R0);
    JUMP_LT(L_exit_vector_set_bang);
    CMP(R1,R2);
    JUMP_GE(L_exit_vector_set_bang);
    MOV(R0,FPARG(2)); // pointer to vector
    ADD(R1,IMM(2));
    MOV(R2,FPARG(4)); //  char to be put instead of previous char
    MOV(INDD(R0,R1),R2);
    MOV(R0," ^ addr_void ^ ");
    POP(FP);
    RETURN;

L_exit_vector_set_bang:
MOV(R0," ^ addr_void ^ ");\n" in
  let rts_vector_set_bang_str = jump_to_cont ^ (callsWrapper rts_vector_set_bang_str) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_rts_vector_set_bang") in
  let rts_vector_set_bang_str = rts_vector_set_bang_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ rts_vector_set_bang_str ^ clcomnt;;
(*-------------------------------- vector-set! ---------------------------- *)
(*++++++++++++++++++++++++++++++++ string->symbol ++++++++++++++++++++++++++++ *)
let rts_string_to_symbol var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ string->symbol ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ string->symbol ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_rts_string_to_symbol:" in
  let addr_in_var_free_table = find_func_addrs "string->symbol" var_free_table in
  let string_to_symbol_str = 
  "   MOV(R0,IMM(-1));
    CMP(INDD(R8,IMM(1)),R0); // check if linked list is empty
    JUMP_EQ(L_list_is_empty);
    // not empty -> run on all links and search for string
    MOV(R0,INDD(FPARG(2),1)); // length of input string.
L_search_in_links_loop:
    MOV(R1,INDD(R8,IMM(1))); // pointer to symbol in current link.
    MOV(R1,INDD(R1,IMM(1)));
    CMP(R0,INDD(R1,IMM(1))); // compare length of input string to lentgh of string in link.
    JUMP_EQ(L_sts_compare_chars); // if length is equal, compare each char.
    ADD(R8,IMM(3));
    CMP(INDD(R8,IMM(-1))," ^ addr_nil ^ "); // last link
    JUMP_NE(L_search_in_links_loop);
    JUMP(L_list_is_empty);

L_sts_compare_chars:
  MOV(R2,FPARG(2)); // R2 = POINTER TO INPUT T_STRING
  ADD(R2,IMM(2));
  ADD(R1,IMM(2));
  MOV(R3,IMM(0)); // i = 0

L_sts_compare_chars_loop_start:
  CMP(R3,R0);
  JUMP_GE(L_sts_compare_chars_loop_end);
  CMP(R1,R2);
  JUMP_NE(L_sts_compare_chars_loop_break);
  ADD(R3,IMM(1));
  ADD(R1,IMM(1));
  ADD(R2,IMM(1));
  JUMP(L_sts_compare_chars_loop_start);

//found string (all compared chars are equal)
L_sts_compare_chars_loop_end:
  MOV(R0,INDD(R8,1));
  JUMP(L_exit_string_to_symbol);
// not found - some chars arent equal
L_sts_compare_chars_loop_break:
    ADD(R8,IMM(3));
    JUMP(L_search_in_links_loop);;

  // creates a new symbol - FINISHED
L_list_is_empty:
    PUSH(2);
    CALL(MALLOC);
    DROP(1);
    MOV(IND(R0),T_SYMBOL);
    MOV(INDD(R0,1),FPARG(2)); // pointer to t_string

L_exit_string_to_symbol:" in
  let string_to_symbol_str = jump_to_cont ^ (callsWrapper string_to_symbol_str) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_rts_string_to_symbol") in
  let string_to_symbol_str = string_to_symbol_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ string_to_symbol_str ^ clcomnt;;
(*-------------------------------- string->symbol ---------------------------- *)
(*++++++++++++++++++++++++++++++++ symbol->string ++++++++++++++++++++++++++++ *)
let rts_symbol_to_string var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ symbol->string ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ symbol->string ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_rts_symbol_to_string:" in
  let addr_in_var_free_table = find_func_addrs "symbol->string" var_free_table in
  let symbol_to_string_str = 
  "    MOV(R0,INDD(FPARG(2),1));
  " in
  let symbol_to_string_str = jump_to_cont ^ (callsWrapper symbol_to_string_str) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_rts_symbol_to_string") in
  let symbol_to_string_str = symbol_to_string_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ symbol_to_string_str ^ clcomnt;;
(*-------------------------------- symbol->string ---------------------------- *)
(*++++++++++++++++++++++++++++++++ eq? ++++++++++++++++++++++++++++ *)
let rts_isEqual var_free_table = 
  let opcomnt = "\n\t/* ++++++++++++ eq? ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ eq? ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_rts_isEqual:" in
  let addr_in_var_free_table = find_func_addrs "eq?" var_free_table in
  let isEqual_str = 
  "
MOV(R1,FPARG(2));
MOV(R2,FPARG(3));
CMP(IND(R1),IMM(T_FRACTION));
JUMP_EQ(L_prim_rts_isEqual_compare_fraction);
CMP(IND(R1),IMM(T_BOOL));
JUMP_EQ(L_prim_rts_isEqual_compare_field);
CMP(IND(R1),IMM(T_NIL));
JUMP_EQ(L_prim_rts_isEqual_compare_field);
CMP(IND(R1),IMM(T_VOID));
JUMP_EQ(L_prim_rts_isEqual_compare_field);
CMP(IND(R1),IMM(T_INTEGER));
JUMP_EQ(L_prim_rts_isEqual_compare_field);
CMP(IND(R1),IMM(T_CHAR));
JUMP_EQ(L_prim_rts_isEqual_compare_field);
CMP(IND(R1),IMM(T_SYMBOL));
JUMP_EQ(L_prim_rts_isEqual_compare_field);
CMP(R1,R2);
JUMP_NE(L_prim_rts_isEqual_false);
MOV(R0," ^ addr_true ^ ");
JUMP(L_prim_rts_isEqual_exit);

L_prim_rts_isEqual_compare_fraction:
CMP(INDD(R1,1),INDD(R2,1));
JUMP_NE(L_prim_rts_isEqual_false);
CMP(INDD(R1,2),INDD(R2,2));
JUMP_NE(L_prim_rts_isEqual_false);
MOV(R0," ^ addr_true ^ ");
JUMP(L_prim_rts_isEqual_exit);

L_prim_rts_isEqual_compare_field:
CMP(INDD(R1,1),INDD(R2,1));
JUMP_NE(L_prim_rts_isEqual_false);
MOV(R0," ^ addr_true ^ ");
JUMP(L_prim_rts_isEqual_exit);

L_prim_rts_isEqual_false:
MOV(R0," ^ addr_false ^ ");

L_prim_rts_isEqual_exit:
  " in
  let isEqual_str = jump_to_cont ^ (callsWrapper isEqual_str) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_rts_isEqual") in
  let isEqual_str = isEqual_str ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ isEqual_str ^ clcomnt;;
(*-------------------------------- eq? ---------------------------- *)
(*++++++++++++++++++++++++++++++++ apply ++++++++++++++++++++++++++++ *)
let rts_apply var_free_table const_table = 
  let opcomnt = "\n\t/* ++++++++++++ apply ++++++++++++ */"in
  let clcomnt = "\n\t/* ------------ apply ------------ */"in
  let cont_label = make_cont_labels() in
  let jump_to_cont = "\n\n\tJUMP(" ^ cont_label ^ ");\n\nL_prim_apply:" in
  let addr_in_var_free_table = find_func_addrs "apply" var_free_table in
  let (loop_code_label1, loop_end_label1) = make_loop_labels() in
  let (loop_code_label2, loop_end_label2) = make_loop_labels() in
  let apply = 
"\tPUSH(R1);
\tPUSH(R2);
\tPUSH(R3);
\tMOV(R0,FPARG(2));
\tMOV(R1,FPARG(3));
\tMOV(R2,IMM(0));
\tMOV(R3,R2);
" ^ loop_code_label2 ^ ":
\tCMP(R1," ^ (getConstAddress Nil const_table) ^ ");
\tJUMP_EQ(" ^ loop_code_label1 ^ ");
\tPUSH(INDD(R1,1));
\tMOV(R1,INDD(R1,2));
\tADD(R3, 1);
\tJUMP(" ^ loop_code_label2 ^ ");
" ^ loop_code_label1 ^ ":
\tCMP(R2, R3);
\tJUMP_GE(" ^ loop_end_label1 ^ ");
\tSUB(R2,1);
\tSUB(R3,2);
\tMOV(R1,STARG(R2));
\tMOV(STARG(R2),STARG(R3));
\tMOV(STARG(R3),R1);
\tADD(R2,IMM(2));
\tADD(R3,IMM(1));
\tJUMP(" ^ loop_code_label1 ^ ");
" ^ loop_end_label1 ^ ":
\tMOV(R1,SP);
\tSUB(R1,IMM(3));
\tSUB(R1,FP);
\tPUSH(R1);
\tPUSH(IMM(0));
\tCALLA(INDD(R0,2));
\tMOV(R3,IMM(2));
\tADD(R3,STARG(0));
\tDROP(R3);
" ^ loop_end_label2 ^ ":
\tPOP(R3);
\tPOP(R2);
\tPOP(R1);\n" in

  let apply = jump_to_cont ^ (callsWrapper apply) ^ "\n" ^ cont_label ^ ":\n" ^ (wrap_rts_clos "L_prim_apply") in
  let apply = apply ^ "\n\tMOV(IND(" ^ addr_in_var_free_table ^ "),R0);" in
  opcomnt ^ apply ^ clcomnt;;
(*-------------------------------- apply ---------------------------- *)

(* =========================== Lib functions ( run time support) =========================== *)
(* DOESNT WORK FOR NOW. MAYBE WONT NEED THIS.*)



let rec getFreeVarAddress name free_var_table = 
 match free_var_table with
    | [] -> -1
    | (fvar,addrs)::rst -> if name = fvar then addrs else getFreeVarAddress name rst
;;

(*++++++++++++++++++++++++++ Print Expr' +++++++++++++++++++++++++++*)
(* todo remove *)
(* PRINT expr' expr'_to_string*)
let rec expr_tag_to_string expr = 
  match expr with
  | Const' (String str) -> "\"Const' (String " ^ str ^ ")\""
  | Const' (Char c) ->  "\"Const' (Char " ^ char_expttostr c ^ ")\""
  | Const' (Bool b) -> "\"Const' (Bool " ^ string_of_bool b ^ ")\""
  | Const' (Number (Int num)) -> "\"Const' (Number (Int " ^string_of_int num ^ "))\""
  (*| Const' Nil -> "'()"
  | Const' Void -> ""
  | Const' b -> "'" ^ Sexpr.sexpr_to_string b
  | BoxGet' (VarFree' s) -> s
  | BoxGet' (VarParam' (s, _)) -> s
  | BoxGet' (VarBound' (s ,_ ,_)) -> s
  | Box' (VarFree' s) -> s
  | Box' (VarParam' (s, _)) -> s
  | Box' (VarBound' (s ,_ ,_)) -> s
  | BoxSet' ((VarFree' s), exp )-> "(BoxSet' " ^ " " ^ s ^ " " ^ p_helper exp ^ ")"
  | BoxSet' ((VarParam' (s ,_)), exp) -> "(BoxSet' " ^  s ^ " " ^ p_helper exp ^ ")"
  | BoxSet' ((VarBound' (s ,_ ,_)), exp) -> "(BoxSet' " ^  s ^ " " ^ p_helper exp ^ ")"
  | Var' (VarFree' s) -> s
  | Var' (VarParam' (s, _)) -> s
  | Var' (VarBound' (s ,_ ,_)) -> s
  | (If' (pred, do_if_true, (Const' Void))) -> "(if " ^ (p_helper pred) ^ " " ^ (p_helper do_if_true) ^ ")"
  | (If' (pred, do_if_true, do_if_false)) -> "(if " ^ (p_helper pred) ^ " " ^ (p_helper do_if_true) ^ " " ^ (p_helper do_if_false) ^ ")"
  | (Def' (name, value)) -> "(define " ^ (p_helper name) ^ " " ^ (p_helper value) ^ ")"
  | (Set' (name, value)) -> "(set! " ^ (p_helper name) ^ " " ^ (p_helper value) ^ ")"
  | (Seq' lst) -> "(begin " ^ String.concat " " (List.map p_helper lst) ^ ")"
  | (Or' lst) -> "(or " ^ String.concat " "(List.map p_helper lst) ^ ")"
  | (LambdaSimple' (a,sexprs)) -> "(lambda (" ^  (String.concat " " a) ^ ") " ^ (p_helper sexprs) ^ ")"
  | (LambdaOpt' ([], a, b)) -> "(lambda "  ^ a ^ " " ^ p_helper b ^ ")"
  | (LambdaOpt' (l, a, b)) -> "(lambda (" ^ (String.concat " " l) ^ " . " ^ a ^ ") " ^ p_helper b ^ ")"
  | (Applic' (procedure, sexprs)) -> "(" ^ (p_helper procedure)  ^ " " ^ (String.concat " " (List.map p_helper sexprs)) ^ ")"
  | (ApplicTP' (procedure, sexprs)) -> "(" ^ (p_helper procedure)  ^ " " ^ (String.concat " " (List.map p_helper sexprs)) ^ ")"
 *)
  | _ -> raise X_not_yet_implemented

and char_expttostr c = 
  match c with
  | '\012' ->  "#\\page"
  | '\r' -> "#\\return"
  | '\t' -> "#\\tab"
  | '\n' ->  "#\\newline"
  | ' ' ->  "#\\space"
  | _ ->  "#\\" ^ Char.escaped c
;;

(* ------------------------------------- Print Expr' -------------------------------*)


(* Handles code gen for const expressions*)
let cg_const exp const_table = 
  let exp_adrs = getConstAddress exp const_table in
  let comment = "\n\t/* Handles consts: \"" ^ Sexpr.sexpr_to_string exp ^ "\" */\n" in
  comment ^ "\tMOV(R0, " ^ exp_adrs ^ ");";;
(*
let cg_bool b = if b then "\t/*Bool true*/\n\tMOV(R0, " ^ addr_true ^ ");\n" else "\t/*Bool false*/\n\tMOV(R0, " ^ addr_false ^ ");\n"

let cg_string str const_table = 
  let addr_str = getConstAddress (String str) const_table in
  "\t/*String*/\n\tMOV(R0, " ^ addr_str ^ ");\n";;

let cg_char c const_table = 
  let addr_char = getConstAddress (Char c) const_table in
  "\t/*Char*/\n\tMOV(R0, " ^ addr_char ^ ");\n";;

let cg_num num const_table = 
  let addr_num = getConstAddress (Number num) const_table in
  "\t/*Number*/\n\tMOV(R0, " ^ addr_num ^ ");\n";;

let cg_nil = "MOV(R0, " ^ addr_nil ^ ");\n";;

let cg_void = "MOV(R0, " ^ addr_void ^ ");\n";; 

let cg_symbol q const_table = 
  let addr_quote = getConstAddress (Symbol q) const_table in
  "MOV(R0, " ^ addr_quote ^ ");\n";;   

*)
(*Printf.sprintf *)
let cg_if pred do_if_true do_if_false = 
let (do_if_false_label, if_end_label) = make_if_labels() in
pred ^ 
"\n\tCMP(R0, " ^ addr_false ^ ");
\tJUMP_EQ(" ^ do_if_false_label ^ ");\n\t" ^
do_if_true ^ "
\tJUMP(" ^ if_end_label ^ ");\n" ^ 
do_if_false_label ^ ":\n\t" ^
do_if_false ^ "\n" ^
if_end_label ^ ":";;

let cg_or lst = 
  let or_end_label = make_or_labels() in
  let jump_out = 
  "\n\tCMP(R0, " ^ addr_false ^ ");
  \tJUMP_NE(" ^ or_end_label ^ ");\n\t" in
  let ans = (String.concat jump_out lst) ^ "\n" in
  ans ^ or_end_label ^ ":";;

let cg_varfree v free_var_table = 
  let addrs = string_of_int (getFreeVarAddress v free_var_table) in
"\t/* ****Varfree**** */
\t// address of var free is " ^ addrs ^ " 
\tMOV(R1, IMM(" ^ addrs ^ "));
\tMOV(R0, IND(R1));"
;;

let cg_varparam min = 
  "\t /*pvar min=" ^ string_of_int min ^ "*/
  \tMOV(R0,FPARG(" ^ string_of_int (min + 2) ^ "))
  \t /* End pvar min=" ^ string_of_int min ^ "*/";;

let cg_varbound min maj = 
  "\t /*bvar maj=" ^ string_of_int maj ^ " min=" ^ string_of_int min ^ "*/
  \tMOV(R0, FPARG(IMM(0))); /* env */
  \tMOV(R1, IMM(" ^ string_of_int maj ^ "));
  \tMOV(R2, INDD(R0,R1));
  \tMOV(R1, IMM(" ^ string_of_int min ^ "));
  \tMOV(R0, INDD(R2, R1));
    \t /* End bvar maj=" ^ string_of_int maj ^ " min=" ^ string_of_int min ^ "*/\n";;

let rec code_gen e const_table free_var_table env = 
  match e with
  | Const' c -> cg_const c const_table
  | BoxGet' var -> cg_box_get var const_table free_var_table env
  | Box' var -> cg_box var const_table free_var_table env
  | BoxSet' (var, exp)-> cg_box_set var exp const_table free_var_table env
  | Var' (VarFree' s) -> cg_varfree s free_var_table
  | Var' (VarParam' (v, min)) -> cg_varparam min
  | Var' (VarBound' (v ,maj ,min)) -> cg_varbound min maj
  | (If' (pred, do_if_true, do_if_false)) -> cg_if (code_gen pred const_table free_var_table env) (code_gen do_if_true const_table free_var_table env) (code_gen do_if_false const_table free_var_table env)
  | (Def' (Var' (VarFree' name), value)) -> cg_define name value const_table free_var_table env 
  | (Set' (Var' (VarParam' (v, min)), value)) -> cg_set min value const_table free_var_table env
  | (Seq' lst) -> String.concat "\n" (List.map (fun exp -> code_gen exp const_table free_var_table env) lst)
  | (Or' lst) -> cg_or (List.map (fun exp -> code_gen exp const_table free_var_table env) lst)
  | (LambdaSimple' (paramList,body)) -> cg_lambda_simple paramList body const_table free_var_table env
  | (LambdaOpt' (paramList, optPar, body)) -> cg_lambda_opt paramList optPar body const_table free_var_table env
  | (Applic' (procedure, sexprs)) -> cg_applic procedure sexprs const_table free_var_table env
  | (ApplicTP' (procedure, sexprs)) -> cg_applicTP procedure sexprs const_table free_var_table env
  | _ -> begin p "code_gen" (p_helper e) ; raise X_this_should_not_happen ; end

and cg_box_set var exp const_table free_var_table env =
  let cg_var = code_gen (Var' var) const_table free_var_table env in
  let cg_exp = code_gen exp const_table free_var_table env in
 cg_exp ^ "MOV(R6, R0);" ^ cg_var ^ "\tMOV(IND(R0), R6);\n"

and cg_box_get var const_table free_var_table env =
  let cg_var = code_gen (Var' var) const_table free_var_table env in
 cg_var ^ "\tMOV(R0,IND(R0));\n"

and cg_box var const_table free_var_table env =
  let cg_var = code_gen (Var' var) const_table free_var_table env in
 cg_var ^ "\tMOV(R1,R0);\n\tPUSH(IMM(1));\n\tCALL(MALLOC);\n\tDROP(IMM(1));\n\tMOV(IND(R0),R1);"

and cg_set min value const_table free_var_table env = 
let cg_value = code_gen value const_table free_var_table env  in
"\t" ^ cg_value ^ "\tMOV(R1, 2);\n\tADD(R1, " ^ string_of_int min ^ ");\n\tMOV(FPARG(R1), R0);\n\tMOV(R0, " ^ getConstAddress Nil const_table ^ ");\n"

and cg_define name value const_table free_var_table env = 
   let cg_value = (code_gen value const_table free_var_table env) in (* now we have the value of 'value' in R0 *)
   let l1 = "\tMOV(IND("  ^ string_of_int (getFreeVarAddress name free_var_table) ^ "), R0);\n" in 
   let l2 = "\tMOV(R0, "  ^ addr_void ^ ");\n" in
   cg_value ^ l1 ^ l2

and cg_applic procedure sexprs const_table free_var_table env = 
  let applic_end = "\nPUSH(INDD(R0,1));// push the environment onto the stack\n\tCALLA(INDD(R0,2));\n\tDROP(2+STARG(0));\n" in
  let pushes = "\t// start pushing params into current frame" ^
    (String.concat "\t" (List.map (fun x -> (code_gen x const_table free_var_table env) ^ "\n\tPUSH(R0);") (List.rev sexprs)))
      ^ "\n\t/* finished pusing params to fp*/"
       ^ "\n\tPUSH(" ^ string_of_int (List.length sexprs) ^ "); // number of params\n\t" in
  "\n/* START OF APPLIC " ^ p_helper procedure ^ "*/\n" ^ pushes ^ (code_gen procedure const_table free_var_table env) (* TODO ^ "CMP(SOB_TYPE);\n\tJUMP_NE(label-blabla);\n\t"*) ^  applic_end ^ "/*end of applic*/\n"

  and cg_applicTP procedure sexprs const_table free_var_table env = 
 let (loop_code_label, loop_end_label) = make_loop_labels() in 
 let pushes = if (List.length sexprs) == 0 then "" else (String.concat "\t" (List.map (fun x -> (code_gen x const_table free_var_table env) ^ "\n\tPUSH(R0);") (List.rev sexprs)))  in   
pushes ^
"\n\tPUSH(IMM(" ^ string_of_int (List.length sexprs) ^ "));" ^
(code_gen procedure const_table free_var_table env) (* TODO ^ "CMP(SOB_TYPE);\n\tJUMP_NE(label-blabla);\n\t"*) ^
"\n\tPUSH(INDD(R0,IMM(1)));
\tPUSH(FPARG(-1));
\tMOV(R1,FPARG(-2));
\tMOV(R2," ^ string_of_int (List.length sexprs) ^ ");
\tADD(R2,IMM(3))
\tMOV(R4,FP);
\tADD(R4,IMM(2));
\tMOV(R7,FP);
\tSUB(R7,FPARG(1));
\tSUB(R7,IMM(4));
\tSUB(R4,IMM(2));
\tMOV(FP,R7);
\tMOV(R3,IMM(0));
" ^ loop_code_label ^ ":
\tCMP(R2,R3);
\tJUMP_EQ(" ^ loop_end_label ^ ");
\tMOV(R5,FP);
\tADD(R5,R3);
\tMOV(R6,R4);
\tADD(R6,R3);
\tMOV(STACK(R5),STACK(R6));
\tADD(R3,IMM(1));
\tJUMP(" ^ loop_code_label ^ ");
" ^ loop_end_label ^ ":
\tMOV(SP,FP);
\tADD(SP,R2);
\tMOV(FP,R1);
\tJUMPA(INDD(R0,IMM(2)));"

and cg_lambda_simple paramList body const_table free_var_table env = 
  let newParamList = if List.length paramList = 0 then [] else paramList in
  let (closure_code_label, closure_end_label) = make_closure_labels() in
  let num_of_params = (string_of_int (List.length paramList)) in
  let size_of_env = string_of_int (List.length env) in
  let (loop_code_label1, loop_end_label1) = make_loop_labels() in 
  let (loop_code_label2, loop_end_label2) = make_loop_labels() in 
  (*let test_before_body = raise X_not_yet_implemented in *)
  let first_loop =
  "//initiate loop variables
  MOV(R3, IMM(0)); // R3 is i == 0.
\tMOV(R4, IMM(1)); // R4 is j == 1
\tMOV(R5, IMM(" ^ size_of_env ^ ")); //R5 is |env|\n" ^ 
loop_code_label1 ^ ":
\tCMP(R3, R5); // if R3 <= R5 enter loop
\tJUMP_GE(" ^ loop_end_label1 ^ ");
\t\t //Entered loop
\t\tMOV(INDD(R0, R4), INDD(FPARG(0),R3));
\t\tADD(R3, IMM(1));
\t\tADD(R4, IMM(1));
\t\tJUMP(" ^ loop_code_label1 ^ "); \n" ^
loop_end_label1 ^ ":" in
  
  let second_loop = 
  "//init parameters for second for loop\nMOV(R3, IMM(0)); // i = 0
\tMOV(R4, FPARG(1));// R4 == number of params\n" ^ 
loop_code_label2 ^ ":
\t\tMOV(R5, R3); // R5 = i
\t\tADD(R5, IMM(2)); //R5 = R5+2
\t\tMOV(INDD(R0, R3), FPARG(R5)); //changed R0 TO INDD(R1, 1)
\t\tADD(R3, IMM(1));
\t\tCMP(R3, R4);
\t\tJUMP_LT(" ^ loop_code_label2 ^ ");\n" ^
loop_end_label2 ^ ":" in

let helper = if size_of_env = "0" 
              then "\tMOV(IND(R0)," ^ addr_nil ^ "); /* num_of_params = " ^ num_of_params ^ " */\n" 
              else  
"\tMOV(R2, R0);
\t //now i want to add the new parameter list to env in place 0
\tPUSH(FPARG(1));
\tCALL(MALLOC);
\tDROP(1);
\tMOV(IND(R2), R0);
" ^ second_loop in

" /* LambdaSimple - " ^ (String.concat " " paramList ) ^ " - */
\tPUSH(IMM(3));
\tCALL(MALLOC);
\tDROP(1);
\tMOV(IND(R0), T_CLOSURE);
\tMOV(R1, R0);  // put address of closure in r1
\tMOV(R0, IMM(" ^ size_of_env ^ "));
\tADD(R0, IMM(1));
\tPUSH(R0);
\tCALL(MALLOC);
\tDROP(1);
\tMOV(INDD(R1, 1), R0); // put address of start of new env in *(r1+1) which is address on env in current closure
\t" ^ first_loop ^ "
\t"
 ^ helper ^ "
\tMOV(INDD(R1, 2), LABEL(" ^ closure_code_label ^ "));
\tMOV(R0, R1);
\tJUMP(" ^ closure_end_label ^ ");
\n" ^ closure_code_label ^ ":\n\t" ^
  (callsWrapper (code_gen body const_table free_var_table (newParamList::env))) ^ closure_end_label ^ ":\n"
 

and cg_lambda_opt  paramList optPar body const_table free_var_table env = 
  let newParamList = if List.length paramList = 0 then [] else paramList in
  let (closure_code_label, closure_end_label) = make_closure_labels() in
  let num_of_params = (string_of_int (List.length paramList)) in
  let size_of_env = string_of_int (List.length env) in
  let (loop_code_label1, loop_end_label1) = make_loop_labels() in 
  let (loop_code_label2, loop_end_label2) = make_loop_labels() in 
  let (loop_code_label_stack_fix1, loop_end_label_stack_fix1) = make_loop_labels() in 
  let (loop_code_label_stack_fix2, loop_end_label_stack_fix2) = make_loop_labels() in
 let stack_fix =
 "\tCMP(FPARG(1), 0);
\tJUMP_LE(" ^ loop_code_label_stack_fix2 ^ ");
\tMOV(R1, FPARG(1));
\tADD(R1, 1);
\tMOV(R1, FPARG(R1));
\tPUSH(" ^ (getConstAddress Nil const_table) ^ ");
\tPUSH(R1);
\tCALL(MAKE_SOB_PAIR);
\tDROP(2);
\tMOV(R1, FPARG(1)); 
\tSUB(R1, " ^ num_of_params ^ ");
\tSUB(R1, 1);
\tMOV(R2, 0);
" ^ loop_code_label_stack_fix1 ^":
\tCMP(R2,R1);
\tJUMP_GE(" ^ loop_end_label_stack_fix1 ^ ");
\t\tPUSH(R0);
\t\tMOV(R3, FPARG(1)); 
\t\tSUB(R3, R2);
\t\tPUSH(FPARG(R3));
\t\tCALL(MAKE_SOB_PAIR);
\t\tDROP(2);
\t\tADD(R2, 1);
\t\tJUMP(" ^ loop_code_label_stack_fix1 ^ ");
" ^ loop_end_label_stack_fix1 ^ ":
\tMOV(R1, " ^ num_of_params ^ ");
\tADD(R1, 2);
\tMOV(FPARG(R1), R0);
\tJUMP(" ^ loop_end_label_stack_fix2 ^ ");
" ^ loop_code_label_stack_fix2 ^ ":
\tPUSH(" ^ (getConstAddress Nil const_table) ^ ");
\tPUSH(" ^ (getConstAddress Nil const_table) ^ ");
\tCALL(MAKE_SOB_PAIR);
\tDROP(2);
\tJUMP(" ^ loop_end_label_stack_fix1 ^ ");
" ^ loop_end_label_stack_fix2 ^ ":\n" in
  (*let test_before_body = raise X_not_yet_implemented in *)
  let first_loop =
  "//initiate loop variables
  MOV(R3, IMM(0)); // R3 is i == 0.
\tMOV(R4, IMM(1)); // R4 is j == 1
\tMOV(R5, IMM(" ^ size_of_env ^ ")); //R5 is |env|\n " ^
loop_code_label1 ^ ":
\tCMP(R3, R5); // if R3 <= R5 enter loop
\tJUMP_GE(" ^ loop_end_label1 ^ ");
\t\t //Entered loop
\t\tMOV(INDD(R0, R4), INDD(FPARG(0),R3));
\t\tADD(R3, IMM(1));
\t\tADD(R4, IMM(1));
\t\tJUMP(" ^ loop_code_label1 ^ "); \n" ^
loop_end_label1 ^ ":" in
  
  let second_loop = 
  "//init parameters for second for loop\nMOV(R3, IMM(0)); // i = 0
\tMOV(R4, FPARG(1)); // R4 == number of params\n" ^ 
loop_code_label2 ^ ":
\t\tMOV(R5, R3); // R5 = i
\t\tADD(R5, IMM(2)); //R5 = R5+2
\t\tMOV(INDD(R0, R3), FPARG(R5)); //changed R0 TO INDD(R1, 1)
\t\tADD(R3, IMM(1));
\t\tCMP(R3, R4);
\t\tJUMP_LT(" ^ loop_code_label2 ^ ");\n" ^
loop_end_label2 ^ ":" in

let helper = if size_of_env = "0" 
              then "\tMOV(IND(R0)," ^ addr_nil ^ "); /* num_of_params = " ^ num_of_params ^ " */\n" 
              else  
"\tMOV(R2, R0);
\t //now i want to add the new parameter list to env in place 0
\tPUSH(FPARG(1));
\tCALL(MALLOC);
\tDROP(1);
\tMOV(IND(R2), R0);
" ^ second_loop in

" /* LambdaSimple - " ^ (String.concat " " paramList ) ^ " - */
\tPUSH(IMM(3));
\tCALL(MALLOC);
\tDROP(1);
\tMOV(IND(R0), T_CLOSURE);
\tMOV(R1, R0);  // put address of closure in r1
\tMOV(R0, IMM(" ^ size_of_env ^ "));
\tADD(R0, IMM(1));
\tPUSH(R0);
\tCALL(MALLOC);
\tDROP(1);
\tMOV(INDD(R1, 1), R0); // put address of start of new env in *(r1+1) which is address on env in current closure
\t" ^ first_loop ^ "
\t"
 ^ helper ^ "
\tMOV(INDD(R1, 2), LABEL(" ^ closure_code_label ^ "));
\tMOV(R0, R1);
\tJUMP(" ^ closure_end_label ^ ");
\n" ^ closure_code_label ^ ":\n\t" ^
  (callsWrapper (stack_fix ^ (code_gen body const_table free_var_table (newParamList::env)))) ^ closure_end_label ^ ":\n"
;;
  
  
(*----------------------------------------------------SYMBOL VARIABLE TABLE----------------------------------------------------*)

let rec symbols_from_constable const_table sym_list = 
  match const_table with
  | [] -> sym_list;
  | frst :: rst -> match frst with
                   | (Symbol s, adrs, ["T_SYMBOL"; adrs_string]) -> symbols_from_constable rst sym_list@[string_of_int adrs] (* was [s,adrs_string] *)
                   | _ -> symbols_from_constable rst sym_list;;
  
(*----------------------------------------------------SYMBOL VARIABLE TABLE----------------------------------------------------*)
(*----------------------------------------------------CONST TABLE----------------------------------------------------*)

(*
 let incadrs_const oldadrs inc_by = 
  let inc = address := (!address + inc_by) in
  (!address - inc_by);;
*) 

let rec build_const_table_helper const_table const_list =
  match const_list with
  | [] -> List.rev const_table
  | frst::rst -> let updated_const_table =  (create_ct_member frst const_table)::const_table in build_const_table_helper updated_const_table rst
															 
(* begin address := (!address + !constParams); !address - !constParams; end *)
and create_ct_member const const_table = const, (incadrs !const_end_address !constParams 0) (*begin address := (!address + !constParams); !address - !constParams; end *), list_of_tuple_for_ct const const_table
																		
and list_of_tuple_for_ct cur_const const_table = 
  match cur_const with
  | Void -> begin constParams := 1; ["T_VOID"]; end
  | Bool b -> begin constParams := 2; ["T_BOOL";if b then "1" else "0"]; end
  | Nil -> begin constParams :=  1; ["T_NIL"]; end
  | Number (Int n) -> begin constParams := 2; ["T_INTEGER";Pervasives.string_of_int n]; end (* TODO Scmint???*)
  | Number (Fraction {numerator; denominator}) -> begin constParams := 3; ["T_FRACTION" ; Pervasives.string_of_int numerator ; Pervasives.string_of_int denominator]; end
  | Char c -> begin constParams := 2; ["T_CHAR";Pervasives.string_of_int (Char.code c)]; end
  | String s -> begin constParams := (String.length s) + 2; ["T_STRING"; Pervasives.string_of_int  (String.length s)]@List.map (fun c -> Pervasives.string_of_int (Char.code c)) (string_to_list s); end
  (*| String s -> begin constParams := 2; ["T_STRING"; s]; end (* TODO no sure if list of chars of the string or the string itself *) *)
  | Symbol s -> begin let params = !constParams in constParams := 2; ["T_SYMBOL"; Pervasives.string_of_int (!const_end_address - params)]; end
  | Pair (a,b) -> begin constParams := 3; ["T_PAIR"; getConstAddress a const_table; getConstAddress b const_table]; end
  | Vector v ->  ["T_VECTOR"]@(ct_handle_vector const_table v)

(*
and get_const_address const_table const =
  (*let frst::rst = if (List.length const_table) = 0 then [(Nil, 0, ["Dummy"]); (Nil, 0, ["Dummy"]) ] else const_table in  *)
  let frst::rst = const_table in
  let (found, ans) = check_if_current frst const in if found then ans else get_const_address rst const

and check_if_current lst_mem const = 
  let typ,adrs,l = lst_mem in if const = typ then (true,adrs) else (false,0) *)
								     
(*Code_Gen.ct_handle_vector [Pair (Symbol "c", Nil); Symbol "a"];;*)
and ct_handle_vector const_table lst = 
  let listLength = List.length lst in
  (* let setParam = constParams := listLength + 2 in *)
  let ret_list = constParams := listLength + 2; [Pervasives.string_of_int listLength]@List.map (fun x -> getConstAddress x const_table) lst in
  ret_list;;
  
(*
takes a nested pair and returns a list of all its sub expressions
test: Code_Gen.handle_nested_const (Pair (Symbol "a", Pair (Symbol "b", Pair (Symbol "c", Nil))));;
Code_Gen.handle_nested_const (Pair(Bool true,Bool false));;
Code_Gen.handle_nested_const (Vector [Symbol "a"; Symbol "b"; Symbol "c";Pair(Bool true,Bool false)]);;
*)
(* (Vector [Symbol "a"; Symbol "b"; Symbol "c"]) *)
let rec handle_nested_const nested_const = 
  match nested_const with
  | Pair(a,b) -> (handle_nested_const a@handle_nested_const b)@[Pair(a,b)]
  | Vector v -> List.flatten (List.map handle_nested_const v)@[Vector v] (* TODO - CHECK IF THIS WORKS*)
  | a -> [a];;

(* removes duplicate expressions from a list
   test: Code_Gen.remove_doubles [Symbol "a"; Symbol "a";
   Pair (Symbol "a", Pair (Symbol "b", Pair (Symbol "c", Nil)))];;
 *)
let rec remove_dups parsed_list =
  match parsed_list with
  | [] -> []
  | frst::rst -> frst::(remove_dups (List.filter (fun x -> x<>frst) rst));;
  
(* extract all consts nested in expr' consts into the const list*)
(*let extract_consts expr const_lst=
  let rec run expr const_lst = 
    match expr with
    | Const' (Symbol s) -> const_lst@[String s; Symbol s]
    | Const' x -> const_lst@[x]
    | BoxSet' ((VarFree' s), exp )-> run exp const_lst
    | BoxSet' ((VarParam' (s ,_)), exp) -> run exp const_lst
    | BoxSet' ((VarBound' (s ,_ ,_)), exp) -> run exp const_lst
    | (If' (pred, dit, (Const' Void))) -> (*run dit (run pred const_lst)*) ((const_lst@run pred [])@run dit [])
    | (If' (pred, dit, dif)) -> let new_const_lst = run dit (run pred const_lst) in run dif new_const_lst
    | (Def' (name, value)) -> (*run value (run name const_lst) *)   let new_const_lst = run name const_lst in run value new_const_lst
    | (Set' (name, value)) -> run value (run name const_lst)
    | (Seq' lst) -> (const_lst@List.flatten (List.map (fun x -> run x []) lst))
    | (Or' lst) -> (const_lst@List.flatten (List.map (fun x -> run x []) lst))
    | (LambdaSimple' (a,sexprs)) -> run sexprs const_lst
    | (LambdaOpt' ([], a, b)) -> run b const_lst
    | (LambdaOpt' (l, a, b)) -> run b const_lst
    | (Applic' (procedure, sexprs)) -> (run procedure const_lst@(List.flatten (List.map (fun x -> run x []) sexprs)))
    | (ApplicTP' (procedure, sexprs)) -> (run procedure const_lst@(List.flatten (List.map (fun x -> run x []) sexprs)))
    | _ -> const_lst in 
    run expr const_lst;; *)


(* extract all consts nested in expr' consts into the const list*)
let extract_consts expr const_lst=
  let rec run expr const_lst = 
    match expr with
    | Const' (Symbol s) -> const_lst@[String s; Symbol s]
    | Const' (Pair(a,b)) -> const_lst@((run (Const' a) []@run (Const' b) [])@[Pair(a,b)])  (*(handle_nested_const a@handle_nested_const b)@[Pair(a,b)] *)
    | Const' (Vector v) ->  const_lst@(List.flatten (List.map (fun vi -> run (Const' vi) []) v)@[Vector v])  (*List.flatten (List.map handle_nested_const v)@[Vector v] (* TODO - CHECK IF THIS WORKS*) *)
    | Const' x -> const_lst@[x]
    | BoxSet' ((VarFree' s), exp )-> run exp const_lst
    | BoxSet' ((VarParam' (s ,_)), exp) -> run exp const_lst
    | BoxSet' ((VarBound' (s ,_ ,_)), exp) -> run exp const_lst
    | (If' (pred, dit, (Const' Void))) -> (*run dit (run pred const_lst)*) ((const_lst@run pred [])@run dit [])
    | (If' (pred, dit, dif)) -> let new_const_lst = run dit (run pred const_lst) in run dif new_const_lst
    | (Def' (name, value)) -> (*run value (run name const_lst) *)   let new_const_lst = run name const_lst in run value new_const_lst
    | (Set' (name, value)) -> run value (run name const_lst)
    | (Seq' lst) -> (const_lst@List.flatten (List.map (fun x -> run x []) lst))
    | (Or' lst) -> (const_lst@List.flatten (List.map (fun x -> run x []) lst))
    | (LambdaSimple' (a,sexprs)) -> run sexprs const_lst
    | (LambdaOpt' ([], a, b)) -> run b const_lst
    | (LambdaOpt' (l, a, b)) -> run b const_lst
    | (Applic' (procedure, sexprs)) -> (run procedure const_lst@(List.flatten (List.map (fun x -> run x []) sexprs)))
    | (ApplicTP' (procedure, sexprs)) -> (run procedure const_lst@(List.flatten (List.map (fun x -> run x []) sexprs)))
    | _ -> const_lst in 
    run expr const_lst;;


 (* let expand_symbol_to_stringsymbol expr const_lst = *)  
let build_const_and_symbol_table parsed_list = 
  let basic_const_list = [Void; Nil; Bool true; Bool false] in
  let second_const_list = List.flatten (List.map (fun x -> extract_consts x []) parsed_list) in (* create a const list from expression list and remove duplicates*)
  let const_list = remove_dups (basic_const_list@second_const_list) in (* TODO - CHECK IF NEED TO REMOVE DUPS TWICE *)
  let const_list  = List.map (fun x -> handle_nested_const x) const_list in (*extract consts from nested pair and vector *)
  (* TODO run all const list and for every Symbol s add  [String s; Symbol s] *)
  let const_list = List.flatten const_list in
  let const_list = remove_dups const_list in
  let const_table = build_const_table_helper [] const_list in
  let symbol_table = List.rev (symbols_from_constable const_table []) in
  (*let set_address = *)varfree_end_address := (!const_end_address + (if (List.length symbol_table == 0) then 3 else ((List.length symbol_table) * 3)));
  (const_table,symbol_table);;


(*let build_const_and_symbol_table parsed_list = 
  let basic_const_list = [Void; Nil; Bool true; Bool false] in
  let second_const_list = List.flatten (List.map (fun x -> extract_consts x []) parsed_list) in (* create a const list from expression list and remove duplicates*)
  let const_list = remove_dups (basic_const_list@second_const_list) in (* TODO - CHECK IF NEED TO REMOVE DUPS TWICE *)
  let const_list  = List.map (fun x -> handle_nested_const x) const_list in (*extract consts from nested pair and vector *)
  (* TODO run all const list and for every Symbol s add  [String s; Symbol s] *)
  let const_list = List.flatten const_list in
  let const_list = remove_dups const_list in
  let const_table = build_const_table_helper [] const_list in
  let symbol_table = List.rev (symbols_from_constable const_table []) in
  let set_address = varfree_end_address := !const_end_address in 
  (const_table,symbol_table);;*)

(*----------------------------------------------------CONST TABLE----------------------------------------------------*)
(*----------------------------------------------------GLOBAL VARIABLE TABLE----------------------------------------------------*)

(*
let incadrs_varfree oldadrs inc_by = 
  let inc = cur_address := (!cur_address + inc_by) in
  (!cur_address - inc_by);;
*)

let rec build_var_table_helper var_table var_lst =
  match var_lst with 
  | [] -> var_table
  | frst::rst -> (frst, incadrs !varfree_end_address  1  1(*begin cur_address := !cur_address + 1; !cur_address - 1; end*)) :: build_var_table_helper var_table rst

(* extract all vars nested in expr' into the var list*)
let extract_vars expr var_lst =
  let rec run expr var_lst = 
    match expr with
    | Var' (VarFree' s) -> var_lst@[s]
    | BoxSet' ((VarFree' s), exp )-> run exp var_lst@[s]
    | BoxSet' ((VarParam' (s ,_)), exp) -> run exp var_lst
    | BoxSet' ((VarBound' (s ,_ ,_)), exp) -> run exp var_lst 
    | (If' (pred, dit, (Const' Void))) -> (*run dit (run pred var_lst)*) ((var_lst@run pred [])@run dit [])
    | (If' (pred, dit, dif)) -> let new_const_lst = run dit (run pred var_lst) in run dit new_const_lst
    | (Def' (name, value)) -> run value (run name var_lst)
    | (Set' (name, value)) -> run value (run name var_lst)
    | (Seq' lst) -> (var_lst@List.flatten (List.map (fun x -> run x []) lst))
    | (Or' lst) -> (var_lst@List.flatten (List.map (fun x -> run x []) lst))
    | (LambdaSimple' (a,sexprs)) -> run sexprs var_lst
    | (LambdaOpt' ([], a, b)) -> run b var_lst
    | (LambdaOpt' (l, a, b)) -> run b var_lst
    | (Applic' (procedure, sexprs)) -> (run procedure var_lst@(List.flatten (List.map (fun x -> run x []) sexprs)))
    | (ApplicTP' (procedure, sexprs)) -> (run procedure var_lst@(List.flatten (List.map (fun x -> run x []) sexprs)))
    | _ -> var_lst in 
    run expr var_lst;;

let rec build_global_vars_table parsed_list var_lst = 
  let run_time_support = ["append"; "apply"; "<"; "="; ">"; "+"; "/"; "*"; "-"; "boolean?"; "car"; "cdr"; "char->integer"; "char?"; "cons"; "denominator"; "eq?"; "integer?"; "integer->char"; "list"; "make-string"; "make-vector"; "map"; "not"; "null?"; "number?"; "numerator"; "pair?"; "procedure?"; "rational?"; "remainder"; "set-car!"; "set-cdr!"; "string-length"; "string-ref"; "string-set!"; "string->symbol"; "string?"; "symbol?"; "symbol->string"; "vector"; "vector-length"; "vector-ref"; "vector-set!"; "vector?"; "zero?"] in
  let var_lst = (*TODO: CHECK IF WE NEED TO PUT List.rev *) List.flatten (List.map (fun x -> extract_vars x var_lst) parsed_list) in
  let var_lst = remove_dups (var_lst@ List.rev run_time_support) in (* TODO - CHECK IF NEED TO REMOVE DUPS TWICE *)
  let var_table = List.rev (build_var_table_helper [] var_lst) in
  (* let set_address = *) cur_address := !varfree_end_address; 
  var_table;;
(*----------------------------------------------------GLOBAL VARIABLE TABLE----------------------------------------------------*)
 
let rec const_table_to_string_list_helper lst addrs =
  match lst with
  | [] -> ""
  | car::cdr -> "\tMOV(ADDR(" ^ (string_of_int addrs) ^ "), " ^ car ^ ");\n" ^ (const_table_to_string_list_helper cdr (addrs + 1));;
  
let const_table_to_string const_table = 
  (*let const_table_size = "\tMOV(ADDR(0), " ^ (1000) ^ ");\n" in (*TODO: CHANGE 6 to real size*) *)
  let prim_consts =
  "\tMOV(ADDR(1000), IMM(T_VOID));\n" ^ 
  "\tMOV(ADDR(1001), IMM(T_NIL));\n" ^
  "\tMOV(ADDR(1002), IMM(T_BOOL));\n\tMOV(ADDR(1003), IMM(1));\n" ^
  "\tMOV(ADDR(1004), IMM(T_BOOL));\n\tMOV(ADDR(1005), IMM(0));\n " in
  let rec const_table_to_string_helper const_table =
    match const_table with
    | [] -> ""
    | (e,addrs,lst)::cdr->
       let addrs_string = string_of_int addrs in
       (match lst with      
    (*
  | "T_VOID"::cdr -> "\tMOV(ADDR(" ^ addrs_string ^ "), T_VOID);\n\t#define SOB_VOID 1\n"
  | "T_NIL"::cdr -> "\tMOV(ADDR(" ^ addrs_string ^ "), T_NIL);\n\t#define SOB_Nil 2\n"
  | "T_BOOL"::cdr -> "\tMOV(ADDR(" ^ addrs_string ^ "), T_BOOL);\n\tMOV(ADDR(" ^ (string_of_int (addrs + 1)) ^ "), " ^ (List.hd cdr) ^ ");\n"
  *)
  | "T_VOID"::cdr -> ""
  | "T_NIL"::cdr -> ""
  | "T_BOOL"::cdr -> ""
  | "T_CHAR"::cdr -> "\tMOV(ADDR(" ^ addrs_string ^ "), T_CHAR);\n\tMOV(ADDR(" ^ (string_of_int (addrs + 1)) ^ "), " ^ (List.hd cdr) ^ ");\n"
  | "T_INTEGER"::cdr -> "\tMOV(ADDR(" ^ addrs_string ^ "), T_INTEGER);\n\tMOV(ADDR("^(string_of_int (addrs + 1)) ^ "), " ^ (List.hd cdr) ^ ");\n"
  | "T_FRACTION"::cdr -> "\tMOV(ADDR(" ^ addrs_string ^ "), T_FRACTION);\n\tMOV(ADDR("^(string_of_int (addrs + 1)) ^ "), " ^ (List.hd cdr) ^ ");\n\tMOV(ADDR("^(string_of_int (addrs + 2)) ^ "), " ^ (List.hd (List.tl cdr)) ^ ");\n" (* todo *)
  | "T_STRING"::cdr -> "\tMOV(ADDR(" ^ addrs_string ^ "), T_STRING);\n" ^ const_table_to_string_list_helper cdr (addrs + 1)
  | "T_SYMBOL"::cdr -> "\tMOV(ADDR(" ^ addrs_string ^ "), T_SYMBOL);\n\tMOV(ADDR(" ^ (string_of_int (addrs + 1)) ^ "), " ^ (List.hd cdr) ^ ");\n"
  | "T_PAIR"::cdr -> "\tMOV(ADDR(" ^ addrs_string ^ "), T_PAIR);\n\tMOV(ADDR(" ^ (string_of_int (addrs + 1)) ^ "), " ^ (List.hd cdr) ^ ");\n\tMOV(ADDR(" ^ (string_of_int (addrs + 2)) ^ "), " ^ (List.hd (List.tl cdr)) ^ ");\n"
  | "T_VECTOR"::cdr -> "\tMOV(ADDR(" ^ addrs_string ^ "), T_VECTOR);\n" ^ const_table_to_string_list_helper cdr (addrs + 1)
  | _ -> raise X_this_should_not_happen) ^ (const_table_to_string_helper cdr)
  in (* const_table_size ^ *) "/*\n " ^ prim_consts ^ (const_table_to_string_helper const_table) ^ "*/\n";;

let rec sym_table_list_data sym_tbl acc next_link_adrs= 
  match sym_tbl with
  | [] -> acc
  | frst :: rst -> if rst = [] then sym_table_list_data rst ([(addr_nil)]@[frst]@["T_LINK"]@acc) (int_of_string addr_nil)
                               else sym_table_list_data rst ([(string_of_int next_link_adrs)]@[frst]@["T_LINK"]@acc) (next_link_adrs + 2)
                   
                    (*| (adrs) -> sym_table_list_data rst ([(string_of_int next_link_adrs)]@[adrs]@["T_LINK"]@acc) (next_link_adrs + 2) 
                   
                   (*
                   | (adrs) -> if rst = [] then sym_table_list_data rst ([(string_of_int next_link_adrs)]@[adrs]@["T_LINK"]@acc) (next_link_adrs + 2)
                                           else sym_table_list_data rst ([(string_of_int next_link_adrs)]@[adrs]@["T_LINK"]@acc) (int_of_string addr_nil) *)
                   | _ -> sym_table_list_data rst acc (int_of_string addr_nil);; *)

let rec const_lst_data const_tbl sym_table acc next_link_adrs= 
  match const_tbl with
  (*
  | [] -> sym_table_list_data  sym_table acc next_link_adrs
  *)
  | [] -> if sym_table = [] then ([(addr_nil)]@["-1"]@["T_LINK"]@acc) else sym_table_list_data  sym_table acc next_link_adrs
  | frst :: rst -> match frst with
                   | (exp, adrs, lst) -> const_lst_data rst sym_table (List.rev lst) next_link_adrs@acc
  


let compile_scheme_file_helper = 
"(define list (lambda x x))
(define append
  (letrec ((app2
      (lambda (s1 s2)
        (if (null? s1) s2
      (cons (car s1)
       (app2 (cdr s1) s2)))))
     (appl
      (lambda (s1 s)
        (if (null? s) s1
      (app2 s1 (appl (car s) (cdr s)))))))
    (lambda s
      (if (null? s) '()
    (appl (car s) (cdr s))))))
   
(define el1e2m2e3nt_at-trololo
  (lambda (n l index)
    (if ( = n index)
        (car l)
        (el1e2m2e3nt_at-trololo n (cdr l) (+ index 1)))))

(define list-le1n22g3th-trololo
  (lambda (l n) 
    (if (null? l)
        n
        (list-le1n22g3th-trololo (cdr l) (+ n 1)))))

(define list-rev123e3r4se-trololo
  (lambda (l) 
    (if (null? l)
        '()
        (append (list-rev123e3r4se-trololo (cdr l)) (list (car l))))))




(define foo-l12is35t-trololo
  (lambda (list_of_lists n index f)
    (if (not (null? list_of_lists))
        (if ( = n index)
            (cons (f (el1e2m2e3nt_at-trololo n (car list_of_lists) 0)) (foo-l12is35t-trololo (cdr list_of_lists) n index f))
            (foo-l12is35t-trololo list_of_lists n (+ index 1) f))
        '())))

(define ma1p1-2ppl34-34t3r3o4l5o5lo
  (lambda (f lst) (if (null? lst)
                      lst
                      (cons (f (car lst)) (ma1p1-2ppl34-34t3r3o4l5o5lo f (cdr lst))))))

(define lolm1a1ptrololo
  (lambda (f n ans list_of_lists)
    (if (> n (list-le1n22g3th-trololo list_of_lists 0))
        (ma1p1-2ppl34-34t3r3o4l5o5lo (lambda (x) (apply f x)) (list-rev123e3r4se-trololo ans))
        (lolm1a1ptrololo f (+ n 1) (cons (foo-l12is35t-trololo list_of_lists n 0) ans) list_of_lists)
        )))
(define map
  (lambda (f . lists)  (lolm1a1ptrololo f 0 '() lists)))
";;


(*
#define SIZE_OF_SYMBOL_TABLE " ^ string_of_int ((List.length symbol_table) * 3) ^ "
#define SIZE_OF_CONSTABLE " ^ string_of_int ((!const_end_address - ct_start_address) + (if (List.length symbol_table == 0) then 1 else ((List.length symbol_table) * 3)))  ^ "
#define SIZE_OF_TABLES " ^ string_of_int (!varfree_end_address - ct_start_address) ^ "  // size of const table + var free table
#define FREE_ADDRESS " ^ string_of_int (!varfree_end_address + ((List.length symbol_table) * 3)) ^ "  // size of const table + var free table
#define DO_SHOW 1
*)


 (* TODO: CHANGE TO REAL SIZE OF SIZE_OF_TABLES*) 
let prolog const_table symbol_table = 
  let const_finish_adrs = !const_end_address in
  let size_of_symbol_table = ((List.length symbol_table) * 3) in
  (* let start_addres_of_linked_list = if size_of_symbol_table == 0 then -1 else const_finish_adrs + size_of_symbol_table - 3 in *)
  let start_addres_of_linked_list = const_finish_adrs + (if size_of_symbol_table == 0 then 0 else size_of_symbol_table - 3) in
  (* let size_of_constable = string_of_int ((!const_end_address - ct_start_address) + ((List.length symbol_table) * 3)) in *)
  (* let size_of_tables = string_of_int (!varfree_end_address - ct_start_address) in *)


"#include <stdio.h>
#include <stdlib.h>
#include <string.h> /* TODO DO I NEED THIS? */
#include \"cisc.h\"

#define SIZE_OF_SYMBOL_TABLE " ^ string_of_int ((List.length symbol_table) * 3) ^ "
#define SIZE_OF_CONSTABLE " ^ string_of_int ((!const_end_address - ct_start_address) + (if ((List.length symbol_table) == 0) then 3 else (List.length symbol_table) * 3) )  ^ "
#define SIZE_OF_TABLES " ^ string_of_int (!varfree_end_address - ct_start_address) ^ "  // size of const table + var free table
#define FREE_ADDRESS " ^ string_of_int (!varfree_end_address + ((List.length symbol_table) * 3)) ^ "  // size of const table + var free table
#define DO_SHOW 1

//#define SCMENV (FPARG(0))
//#define SCMNARGS (FPARG(1))
//#define SCMARG(n) (FPARG(n+2)) //n'th argument

int main() 
{
    START_MACHINE;
    PUSH(IMM(0)); //GLOBAL ENV
    PUSH(IMM(0));
    PUSH(FP);
  JUMP(CONTINUE);
  #include \"char.lib\"
  #include \"io.lib\"
  #include \"math.lib\"
  #include \"string.lib\"
  #include \"system.lib\"
  #include \"scheme.lib\"" ^ "/*  (* UNCOMMENT *) more_code */" ^ "
  #include \"debug_macros.h\"   

CONTINUE:;
  long mem_init[SIZE_OF_CONSTABLE]={" ^ (String.concat ","   (List.rev (const_lst_data const_table symbol_table [] const_finish_adrs))) ^ "};
  memcpy(&IND("  ^ string_of_int ct_start_address ^ "),mem_init,SIZE_OF_CONSTABLE*sizeof(long));
  PUSH(IMM(FREE_ADDRESS)); // TODO ORIAN - I CHANGED FROM SIZE_OF_TABLES
  MOV(R8,IMM(" ^ string_of_int start_addres_of_linked_list ^")) // " ^ string_of_int (List.length symbol_table) ^ "
  CALL(MALLOC);
  DROP(1);";;
  
let epiloge = 
"   PUSH(R0);
    MOV(R1,IMM(" ^ addr_void ^"));
    CMP(R0,R1);
    JUMP_NE(L_do_print_sob);
    JUMP(L_do_not_print_sob);
    /*printf(\" +++++ IN epiloge %ld +++++ \\n\", R0); */
L_do_print_sob:
    CALL(WRITE_SOB);
    /*printf(\"\\n ----- IN epiloge ----- \\n\");*/
L_do_not_print_sob:
    STOP_MACHINE;\
    return 0;
    }";;
  
let output_file_wrapper str const_table vars_table symbol_table = 
  let vars_table_string = "\t" ^ (String.concat "\n\t" (List.map (fun (v,addrs) -> "MOV(IND(" ^ string_of_int addrs ^"), T_UNDEFINED);") vars_table)) ^ "\n" in
  let symbol_table_string = "" in
    let more_code = rts_apply vars_table const_table ^  rts_isEqual vars_table ^ rts_symbol_to_string vars_table ^ rts_string_to_symbol vars_table ^
     rts_vector_set_bang vars_table ^ rts_string_set_bang vars_table ^ rts_vector_ref vars_table ^ rts_string_ref vars_table ^ rts_vector vars_table ^ rts_greater_then vars_table const_table
     ^  rts_less_then vars_table const_table ^ rts_equal vars_table const_table ^ rts_mul vars_table ^ rts_minus vars_table ^ rts_plus vars_table ^ 
    rts_make_vector vars_table ^ rts_make_string vars_table ^ rts_remainder vars_table ^ rts_numerator vars_table ^ rts_denominator vars_table ^ rts_div vars_table ^ rts_integer_to_char vars_table 
    ^ rts_vector_length vars_table ^ rts_string_length vars_table ^ rts_char_to_integer vars_table ^ rts_not vars_table ^ rts_set_cdr_bang vars_table ^ rts_set_car_bang vars_table ^ rts_isZero vars_table
     ^ rts_isProcedure vars_table ^ rts_isVector vars_table ^ rts_isPair vars_table ^
   rts_isSymbol vars_table ^ rts_isString vars_table ^ rts_isChar vars_table ^ rts_isRational vars_table ^ rts_isNumber vars_table ^
    rts_isInteger vars_table ^ rts_isBoolean vars_table ^ rts_isNull vars_table ^ rts_cdr vars_table ^ rts_car vars_table ^ rts_cons vars_table in
  (prolog const_table symbol_table) ^ (const_table_to_string const_table) ^ vars_table_string ^ symbol_table_string ^ more_code ^  "\t" ^ str ^ epiloge;;
  
let cttmp scm_source_file =
  let str_in = file_to_string scm_source_file in (* Read input file(Scheme) *) 
  let expr_list = Tag_Parser.read_expressions (compile_scheme_file_helper ^ str_in) in (* Tag parse *)
  let parsed_list = List.map Semantics.run_semantics expr_list in (* Semantic analysis *)
  let (ctab,symtab) = build_const_and_symbol_table parsed_list in (* Build constant table - see 'Constant table explanation' in README*) 
  let gvtab = build_global_vars_table  parsed_list [] in
  (*const_table_to_string ctab;;*)
  ctab,symtab,gvtab;;


 let compile_scheme_file scm_source_file asm_target_file =
  let str_in = file_to_string scm_source_file in (* Read input file(Scheme) *) 
  let expr_list = Tag_Parser.read_expressions (compile_scheme_file_helper ^ str_in) in (* Tag parse *)
  let parsed_list = List.map Semantics.run_semantics expr_list in (* Semantic analysis *)
  let (const_table, symbol_table) = build_const_and_symbol_table parsed_list in (* Build constant table - see 'Constant table explanation' in README *)
  let vars_table = build_global_vars_table  parsed_list [] in
  (* TODO list of touples ("name of func" , counter + 1) of run_time)support and varfree *)
  (* implement c file in which i write label (capital letter) and the implementation of the primitive. 
  then i include it in prolog.*)
  
  let str_out_unwrapped = String.concat "\n" (List.map (fun e -> (code_gen e const_table vars_table [])) parsed_list) in
  let str_out_wrapped = output_file_wrapper str_out_unwrapped const_table vars_table symbol_table in
  string_to_file asm_target_file str_out_wrapped;;
    
 end;;
   
