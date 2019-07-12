(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;

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


let _tag_parse_boolean_ sexpr= Const(Sexpr(sexpr));;
let _tag_parse_char_ sexpr= Const(Sexpr(sexpr));;
let _tag_parse_number_ sexpr= Const(Sexpr(sexpr));;
let _tag_parse_string_ sexpr= Const(Sexpr(sexpr));;
let _tag_parse_quote_ sexpr= Const(Sexpr(sexpr));;
let _tag_parse_variable_ s = Var(s);;
let _tag_parse_symbol_ s = Const(Sexpr(s));;

let _tag_parse_const_void_ = Const(Void);;
let _tag_parse_sequence_ exprs = Seq(exprs);;


let rec _def_to_dummy_def_ lst =  match lst with
| Nil -> Nil
| Pair(Pair(a,Pair(b, Nil)),rest) ->  Pair(Pair(a,Pair(Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil)), _def_to_dummy_def_ rest)
| _ -> failwith "def list is worng" ;;

let rec _def_to_set_list_ lst body =  match lst with
| Nil -> body
| Pair(Pair(a,Pair(b, Nil)),rest) ->  Pair(Pair(Symbol("set!"), Pair(a,Pair(b, Nil)))  , _def_to_set_list_ rest body)
| _ -> failwith "def list is worng" ;;

let rec _def_list_to_var_list_ lst =  match lst with
| Nil -> Nil
| Pair( Pair (_var, Pair(_val,Nil) )  , rest) ->  Pair( _var, (_def_list_to_var_list_ rest))
| _ -> failwith "def list is worng" ;;

let rec _def_list_to_val_list_ lst =  match lst with
| Nil -> Nil
| Pair( Pair (_var, Pair(_val,Nil) )  , rest) ->  Pair (_val ,(_def_list_to_val_list_ rest))
| _ -> failwith "def list is worng" ;;


 let rec get_last_element lst= match lst with
        | []    -> failwith "empty list"
        | last::[] -> last
        | _::next -> get_last_element next


let rec del_last_element lst = match lst with
        | [] -> failwith "empty list"
        | x::last::[] -> x::[]
        | last::[] -> []
        | curr::next -> curr :: (del_last_element next)

let _is_args_list_ lst  = let rec _rec_is_args_list_ lst args  = match lst with
                          | Pair (Symbol(arg), rst) when not (List.mem arg args)  -> (_rec_is_args_list_ rst (arg::args))
                          | Nil -> true
                          | _ -> false in

    _rec_is_args_list_ lst [] ;;




let _is_opt_arg_list_ lst  = let rec _rec_is_opt_args_list_ lst args  = match lst with
                          | Pair (Symbol(arg), rst) when not (List.mem arg args) -> (_rec_is_opt_args_list_ rst (arg::args))
                          | Symbol(arg)  when not (List.mem arg args)  -> true
                          | _ -> false in

    _rec_is_opt_args_list_ lst [] ;;

let _is_nil_ x = match x with
  | Nil -> true
  | _ -> false;;

let rec _symbol_list_to_string_list_ lst = match lst with
  | Nil -> []
  | Pair (Symbol(str), rst) -> str :: (_symbol_list_to_string_list_ rst)
  | _ -> raise X_syntax_error (*we are not spose to get here *)


  let rec _symbol_list_to_string_list_opt_ lst = match lst with
  | Pair (Symbol(str), rst) -> str :: (_symbol_list_to_string_list_opt_ rst)
  | Symbol(str) -> []
  | _ -> raise X_syntax_error (*we are not spose to get here *)


  let rec _symbol_list_to_last_element_ lst = match lst with
  | Pair (Symbol(str), rst) -> _symbol_list_to_last_element_ rst
  | Symbol(str) -> str
  | _ -> raise X_syntax_error (*we are not spose to get here *)


  let _tag_parse_applications_ expr exprs = Applic( expr, exprs);;

  let rec _exprs_to_list_ exprs = match exprs with
    | Nil -> []
    | Pair(a,b) -> tag_parse_expression a :: (_exprs_to_list_ b)
    | a -> [tag_parse_expression a]


 and _body_list_to_exper_sec_ lst = match lst with
  | Nil -> []
  | Pair (exprs, rst) -> (tag_parse_expression exprs) :: (_body_list_to_exper_sec_ rst)
  | _ -> raise X_syntax_error (*we are not spose to get here *)

  and _body_exper_ lst = let l = _body_list_to_exper_sec_ lst in
                      match l with 
                      | x::[] -> x
                      | _ -> Seq(l)

 and  _tag_parse_lambda_ _args _body = LambdaSimple(_args ,(_body_exper_ _body) )
 
 and  _tag_parse_lambda_opt_ _args  _body = let _args_without_opt = _symbol_list_to_string_list_opt_ _args in
                                            let _opt = _symbol_list_to_last_element_ _args in
                                            let _body_as_seq = (_body_exper_ _body) in
 
                                 LambdaOpt( _args_without_opt , _opt, _body_as_seq )

and _tag_parse_if_expression_with_else_ _cond _then _else = If((tag_parse_expression _cond),(tag_parse_expression _then),(tag_parse_expression _else))
and _tag_parse_if_expression_without_else_ _cond _then = If((tag_parse_expression _cond),(tag_parse_expression _then),Const(Void))
and  _tag_parse_lambda_ver_ _body = LambdaOpt( [], "vs" , Seq((_body_list_to_exper_sec_ _body)) )

and _tag_parser_or_ lst = let l =  _body_list_to_exper_sec_ lst in
                      match l with 
                      | [] -> Const(Sexpr(Bool(false)))
                      | x::[] -> x
                      | _ -> Or(l) 

and _tag_parser_cond_ ribs = match ribs with
        | Pair(Pair(_cond, Pair(Symbol(_arrow), Pair(__then, Nil))), Nil)when _arrow = "=>" -> Pair (Symbol "let",
        Pair
         (Pair (Pair (Symbol "value", Pair (_cond, Nil)),
           Pair
            (Pair (Symbol "f",
              Pair (Pair (Symbol "lambda", Pair (Nil, Pair (__then, Nil))),
               Nil)),
            Nil)),
         Pair
          (Pair (Symbol "if",
            Pair (Symbol "value",
             Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), Nil))),
          Nil)))
          | Pair(Pair(_cond, Pair(Symbol(_arrow), Pair(__then, Nil))), rst)when _arrow = "=>" -> Pair (Symbol "let",
          Pair
           (Pair (Pair (Symbol "value", Pair (_cond, Nil)),
             Pair
              (Pair (Symbol "f",
                Pair (Pair (Symbol "lambda", Pair (Nil, Pair (__then, Nil))),
                 Nil)),
              Pair
               (Pair (Symbol "rest",
                 Pair (Pair (Symbol "lambda", Pair (Nil, Pair ((_tag_parser_cond_ rst), Nil))),
                  Nil)),
               Nil))),
           Pair
            (Pair (Symbol "if",
              Pair (Symbol "value",
               Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
                Pair (Pair (Symbol "rest", Nil), Nil)))),
            Nil)))
        | Pair(Pair(Symbol(_else), rest),rst) when _else="else" -> Pair(Symbol("begin"),rest)
        | Pair(Pair(_cond, rest),Nil) -> Pair(Symbol("if"), Pair( _cond, Pair( Pair(Symbol("begin"),rest), Nil)))
        | Pair(Pair(_cond, rest),rst) -> Pair(Symbol("if"), Pair( _cond, Pair( Pair(Symbol("begin"),rest), Pair( (_tag_parser_cond_ rst), Nil)))) 
        | _ -> raise X_syntax_error

and _letrec_to_let_  def_list body = let d_lst = _def_to_dummy_def_ def_list in 
                                     let s_lst = _def_to_set_list_  def_list body in 

                                     Pair(Symbol("let"), Pair(d_lst , s_lst))
 
and _tag_parser_define_ _name _sexpr = Def((Var(_name)), (tag_parse_expression _sexpr))
  
and _tag_parser_set_ _name _sexpr = Set((Var(_name)), (tag_parse_expression _sexpr))


and _list_to_pairs_ list = match list with
  | car::cdr -> Pair(car, _list_to_pairs_ cdr)
  | [] -> Nil

        
and _quasiquote_macro_expansion_ second = match second with
  | Pair(Symbol(unquote), Pair(sec, Nil)) when (unquote = "unquote")-> sec
  | Pair(Symbol(unquoteSplicing), Pair(sec, Nil)) when (unquoteSplicing = "unquote-splicing")-> raise X_syntax_error
  | Symbol(a) -> Pair (Symbol "quote", Pair(Symbol(a),Nil))
  
  | Pair(Pair (Symbol "unquote-splicing", Pair (a, Nil)), b) -> let second = _quasiquote_macro_expansion_ b in
                                                                Pair (Symbol "append", Pair (a, Pair(second, Nil)))
  | Pair(a, Pair (Symbol "unquote-splicing", Pair (b, Nil))) -> let first = _quasiquote_macro_expansion_ a in

                                                                Pair (Symbol "cons", Pair (first, Pair(b, Nil)))
  | Pair(a, b) -> let first = _quasiquote_macro_expansion_ a in
                  let second = _quasiquote_macro_expansion_ b in
                  Pair (Symbol "cons", Pair (first, Pair(second, Nil)))
  | Nil -> Pair (Symbol "quote", Pair (Nil, Nil))
  | Vector(vectorList) -> Pair(Symbol "vector", (_list_to_pairs_ (List.map _quasiquote_macro_expansion_ vectorList)))
  | String(s) -> String(s)
  | Char(c) -> Char(c)
  | Number(Int(n)) -> Number(Int(n))
  | _ -> raise X_syntax_error


       
       
and _and_macro_expansion_ second = match second with
  | Nil -> Bool(true)
  | Pair(a,Nil) -> a
  | Pair(a,b) ->  let _b = _and_macro_expansion_ b in
                  Pair(Symbol "if", Pair( a, Pair( _b, Pair(Bool(false), Nil))))
  | _ -> raise X_syntax_error



       
and _letstar_to_let_ def_list body =  match def_list with 
  | Nil-> (Pair(Symbol("let"), Pair(Nil , body)))
  | Pair(Pair(a,b), Nil )  ->  (Pair(Symbol("let"), Pair(Pair(Pair(a,b), Nil ) , body)))
  | Pair(Pair(a,b), rest )  -> (Pair(Symbol("let"), Pair(Pair(Pair(a,b), Nil ) , Pair( (_letstar_to_let_ rest body ) ,Nil))))
  | _ -> raise X_syntax_error
                           
and tag_parse_expression sexpr = match sexpr with
  | Bool(b) -> _tag_parse_boolean_ sexpr
  | Char(c) -> _tag_parse_char_ sexpr
  | Number(n) -> _tag_parse_number_ sexpr
  | String(s) -> _tag_parse_string_ sexpr
               
  | Pair(Symbol(andSymbol), sec) when (andSymbol = "and") -> tag_parse_expression (_and_macro_expansion_ sec)
  | Pair(Symbol(s), Pair(x, Nil)) when (s = "quote") -> _tag_parse_quote_ x
  | Pair(Symbol(quasiquote), Pair(Symbol(sec), Nil)) when (quasiquote = "quasiquote") -> _tag_parse_symbol_ (Symbol(sec))
                                                                                       
  | Pair(Symbol(quasiquote), Pair(sec, Nil)) when (quasiquote = "quasiquote") -> tag_parse_expression (_quasiquote_macro_expansion_ sec)


                                                                               
  | Symbol(s) when not(List.mem s reserved_word_list)(*AND NOT STARTING WITH , ...*) -> _tag_parse_variable_ s
  (* handling if *)
  | Pair(Symbol(s), Pair( _cond, Pair( _then, Pair(_else, Nil)))) when (s = "if") -> _tag_parse_if_expression_with_else_ _cond _then _else
  | Pair(Symbol(s), Pair( _cond, Pair( _then, Nil))) when (s = "if") -> _tag_parse_if_expression_without_else_ _cond _then
  (* handling lambda *)          
  | Pair(Symbol(lambda), Pair( _args, _body )) when  ( lambda = "lambda"  ) && (_is_args_list_ _args) && (not(_is_nil_ _body) )  -> _tag_parse_lambda_ (_symbol_list_to_string_list_ _args) _body
  | Pair(Symbol(lambda), Pair( _args, _body )) when  ( lambda = "lambda"  ) && (_is_opt_arg_list_ _args) && (not(_is_nil_ _body) )  -> _tag_parse_lambda_opt_ _args _body
  | Pair(Symbol(lambda), Pair( Symbol(vs), _body )) when  ( lambda = "lambda"  ) && (vs  = "vs") && (not(_is_nil_ _body) )  -> _tag_parse_lambda_ver_  _body
  (* handling or *)
  | Pair(Symbol(_or), _list) when _or = "or" -> _tag_parser_or_ _list
  (* handling definitions *)
  | Pair(Symbol(_define), Pair(Symbol(_name),Pair(_sexpr, Nil))) when _define = "define"  && (not (List.mem _name reserved_word_list)) -> _tag_parser_define_ _name _sexpr

  (* handling set *)
  | Pair(Symbol(_set), Pair(Symbol(_name),Pair(_sexpr, Nil))) when _set = "set!"  && (not (List.mem _name reserved_word_list)) -> _tag_parser_set_ _name _sexpr
   (* handling MIT def  (define(<name> . <argl>) <expr>) *)
   | Pair(Symbol(_define), Pair(Pair(Symbol(_name) , _arglist ) ,  expr )) when _define = "define"  -> tag_parse_expression (Pair(Symbol(_define), Pair(Symbol(_name),Pair(Pair(Symbol("lambda"), Pair( _arglist, expr )), Nil)))) 
   (* handling let   *)
   | Pair(Symbol(_let), Pair(_def_list , _body)) when _let = "let" -> let lambda_sexpr = Pair(Symbol("lambda"), Pair ((_def_list_to_var_list_ _def_list),_body)) in
                                                                      let vals = _def_list_to_val_list_ _def_list in
                                                                      tag_parse_expression (Pair (lambda_sexpr, vals))

   (* handling let-star   *)
   | Pair(Symbol(_let), Pair(_def_list , _body)) when _let = "let*"  ->  tag_parse_expression (_letstar_to_let_ _def_list _body)
   (* handling letrec *)
   | Pair(Symbol(_let), Pair(_def_list , _body)) when _let = "letrec"  ->  tag_parse_expression (_letrec_to_let_ _def_list _body)
 
   (*handling cond*)
   |Pair(Symbol(_cond),ribs) when _cond="cond" ->  tag_parse_expression (_tag_parser_cond_ ribs)
   

  (* handling seq *)
  | Pair(Symbol(beg), Nil) when (beg = "begin") -> _tag_parse_const_void_
  | Pair(Symbol(beg), Pair(a, Nil)) when (beg = "begin") -> tag_parse_expression a
  | Pair(Symbol(beg), rest) when (beg = "begin") -> let seq = _exprs_to_list_ rest in
                                                      _tag_parse_sequence_ seq
  (* handling app *)
  | Pair(a, b) -> let first = tag_parse_expression a in
                  let rest = _exprs_to_list_ b in
                  _tag_parse_applications_ first rest



 
  | _ -> raise X_syntax_error;; (*NOT SURE*)


let tag_parse_expressions sexpr = (List.map tag_parse_expression sexpr );;


  
end;; (* struct Tag_Parser *)
