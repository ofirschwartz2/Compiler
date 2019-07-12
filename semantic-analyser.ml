(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

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
    | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
    | (Set'(var1, val1), Set'(var2, val2)
    | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                               (expr'_eq val1 val2)
    | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
    | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
       (String.equal var1 var2) &&
         (List.for_all2 String.equal vars1 vars2) &&
           (expr'_eq body1 body2)
    | Applic'(e1, args1), Applic'(e2, args2)
    | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
     (expr'_eq e1 e2) &&
       (List.for_all2 expr'_eq args1 args2)
    | Box'(_), Box'(_) -> true
    | BoxGet'(_), BoxGet'(_) -> true
    | BoxSet'(_, v1), BoxSet'(_, v2) -> expr'_eq v1 v2 
    | _ -> false;;
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let rec _index_in_list_iter_ var p index = match p with
  |  [] -> (-1)
  |  a::b when a = var -> index 
  |  a::b -> _index_in_list_iter_ var b (index + 1);;

let _index_in_list_ var p = _index_in_list_iter_ var p 0;;




let rec _tuple_in_bound_iter_ var b index  = match b with
  | [] -> (-1 ,-1)
  | a::rest -> let index_in_list = _index_in_list_ var a in
            if (index_in_list > -1) then (index ,index_in_list)
            else _tuple_in_bound_iter_ var rest (index + 1);;                                 


 let _tuple_in_bound_list_ var b = _tuple_in_bound_iter_ var b 0;;

 let _var_to_var'_ var p b = let index_in_pram = _index_in_list_ var p in
                             if (index_in_pram > -1) then Var'(VarParam(var, index_in_pram))
                             else let  tuple_in_bound = _tuple_in_bound_list_ var b in
                                  if (-1 <  (fst tuple_in_bound) ) then    Var'(VarBound(var, (fst tuple_in_bound), (snd tuple_in_bound) ))
                                  else Var'(VarFree(var)) ;;

 

 
 

 
  
  let rec _lambda_expr'_ paramsList boundsList e = match e with
      | Const(x) -> Const'(x)
      | Var (x) -> (_var_to_var'_ x paramsList boundsList) 
      | If (x, y, z)-> If'(_lambda_expr'_ paramsList boundsList x, _lambda_expr'_ paramsList boundsList y, _lambda_expr'_ paramsList boundsList z)                                
      | Seq (x) -> let annotate = _lambda_expr'_ paramsList boundsList in
                                   Seq'(List.map annotate x)                             
      | Set (x, y) -> Set'(_lambda_expr'_ paramsList boundsList x, _lambda_expr'_ paramsList boundsList y)
      | Def (x, y) -> Def'(_lambda_expr'_ paramsList boundsList x, _lambda_expr'_ paramsList boundsList y)
      | Or (x) -> Or'( List.map (_lambda_expr'_ paramsList boundsList) x )
      | LambdaSimple (pram, body) -> LambdaSimple'( pram ,( _lambda_expr'_ pram ([paramsList] @ boundsList) body )  ) 
      | LambdaOpt (pram, variadic, body) -> LambdaOpt'( pram, variadic ,(_lambda_expr'_ (pram @ [variadic]) ([paramsList] @ boundsList) body )  ) 
      | Applic (x, y) -> Applic'(_lambda_expr'_ paramsList boundsList x, (List.map (_lambda_expr'_ paramsList boundsList) y))

  
  let rec annotate_lexical_addresses e = match e with
      | Const(x) -> Const'(x)
      | Var (x) -> Var'(VarFree(x))
      | If (x, y, z)-> If'(annotate_lexical_addresses x, annotate_lexical_addresses y, annotate_lexical_addresses z)
      | Seq (x) -> Seq'(List.map annotate_lexical_addresses x)
      | Set (x, y)-> Set'(annotate_lexical_addresses x, annotate_lexical_addresses y)
      | Def (x, y) -> Def'(annotate_lexical_addresses x, annotate_lexical_addresses y)
      | Or (x) -> Or'(List.map annotate_lexical_addresses x)
      | LambdaSimple (pram, body) ->LambdaSimple'( pram, (_lambda_expr'_ pram [] body))
      | LambdaOpt (pram, variadic, body) -> LambdaOpt'( pram, variadic ,(_lambda_expr'_ (pram @ [variadic]) [] body))
      | Applic (x, y) -> Applic' (annotate_lexical_addresses x, List.map annotate_lexical_addresses y)

let rec seq_iter seq = match seq with
      |  [] -> []
      | last::[]  -> (applic'_to_applicTP' last) :: []
      |  element::rest -> (annotate_tail_calls element) :: (seq_iter rest)
   
and applic'_to_applicTP' e = match e with
| Const'(x) -> Const'(x)
| Var'(x) -> Var'(x)
| If'(x, y, z)-> If'(annotate_tail_calls x, applic'_to_applicTP'  y, applic'_to_applicTP'  z)
| Seq'(x) -> Seq'(seq_iter x)
| Set'(x, y)-> Set'(annotate_tail_calls x, annotate_tail_calls y)
| Def'(x, y) -> Def'(annotate_tail_calls x, annotate_tail_calls y)
| Or'(x) -> Or'(seq_iter x)
| LambdaSimple'(pram,body)->LambdaSimple'( pram,applic'_to_applicTP' body )
| LambdaOpt'(pram, variadic, body) -> LambdaOpt'( pram, variadic ,applic'_to_applicTP' body )
| Applic'(x, y) -> ApplicTP' (annotate_tail_calls x, List.map annotate_tail_calls y)
| _ -> failwith "aaaa"

                    
and annotate_tail_calls e = match e with
| Const'(x) -> Const'(x)
| Var'(x) -> Var'(x)
| If'(x, y, z)-> If'(annotate_tail_calls x, annotate_tail_calls y, annotate_tail_calls z)
| Seq'(x) -> Seq'(List.map annotate_tail_calls x)
| Set'(x, y)-> Set'(annotate_tail_calls x, annotate_tail_calls y)
| Def'(x, y) -> Def'(annotate_tail_calls x, annotate_tail_calls y)
| Or'(x) -> Or'(List.map annotate_tail_calls x) 
| LambdaSimple'(pram,body)->LambdaSimple'( pram, applic'_to_applicTP' body )
| LambdaOpt'(pram, variadic, body) -> LambdaOpt'( pram, variadic , applic'_to_applicTP' body)
| Applic'(x, y) ->  Applic'(annotate_tail_calls x, List.map annotate_tail_calls y)
| _ -> e;;




let rec rec_seq_is_set list param = match list with
| last::[] -> (is_set_body last param)
| first::rest -> if (is_set_body first param) then true else  (rec_seq_is_set rest param)
| [] -> false
                    
and is_set_body body param = match body with 
| Const'(x) -> false
| Var'(x) -> false
| If'(x, y, z)-> (is_set_body x param) || (is_set_body y param) || (is_set_body z param)
| Seq'(x) -> (rec_seq_is_set x param)
| Set'(Var'(VarFree(x)), y) -> false 
| Set'(Var'(VarParam(name, i)), y) -> if name = param then true else false
| Set'(Var'(VarBound(name, i, j)), y) -> if name = param then true else false 
| Def'(x, y) -> false
| Or'(x) -> (rec_seq_is_set x param)
| LambdaSimple'(pram,body) -> false
| LambdaOpt'(pram, variadic, body) -> false
| Applic'(x, y) ->  (is_set_body x param) || (rec_seq_is_set y param)
| ApplicTP'(x, y) ->  (is_set_body x param) || (rec_seq_is_set y param)
| BoxSet'(x,e) -> (is_set_body e param) (* think about the senerio when x is param*)
| _ -> false


and is_set lambda param = match lambda with 
| LambdaSimple'(pram,body) -> (is_set_body body param)
| LambdaOpt'(pram, variadic, body) -> (is_set_body body param)
| _ -> failwith " is_set witout lambda";;


let rec rec_seq_is_read list param = match list with
| last::[] -> (is_read_body last param)
| first::rest -> if (is_read_body first param) then true else  (rec_seq_is_read rest param)
| [] -> false
                    
and is_read_body body param = match body with 
| Const'(x) -> false
| Var'(VarParam(name, i)) -> if name = param then true else false
| Var'(VarBound(name, i, j)) -> if name = param then true else false
| If'(x, y, z)-> (is_read_body x param) || (is_read_body y param) || (is_read_body z param)
| Seq'(x) -> (rec_seq_is_read x param)
| Set'(x, y) -> is_read_body y param
| Def'(x, y) -> false
| Or'(x) -> (rec_seq_is_read x param)
| LambdaSimple'(pram,body) -> false
| LambdaOpt'(pram, variadic, body) -> false
| Applic'(x, y) ->  (is_read_body x param) || (rec_seq_is_read y param)
| ApplicTP'(x, y) ->  (is_read_body x param) || (rec_seq_is_read y param)
| BoxSet'(x,e) -> (is_read_body e param) (* think about the senerio when x is param*)
| _ -> false


and is_read lambda param = match lambda with 
| LambdaSimple'(prams,body) -> (is_read_body body param)
| LambdaOpt'(prams, variadic, body) -> (is_read_body body param)
| _ -> failwith " is_read witout lambda";;

(* ****************************************8 *)


let is_x_pram_in_lambda l x = match l with 
| LambdaSimple'(prams,body) -> List.mem x prams 
| LambdaOpt'(prams, variadic, body) -> List.mem x prams || x = variadic
| _ -> failwith " is_x_pram_in_lambda witout lambda";;


let find_read_and_write_only_in_body parentLambda param = let read = is_read parentLambda param in
                                                          let write = is_set parentLambda param in
                                                          [[read ; write]];;

let  rec _find_read_and_write_for_all_sons_body_inside_seq exprList param retList = match exprList with
| [] -> retList
| first::rest -> let firstRes = _find_read_and_write_for_all_sons_body_ first param retList in
                _find_read_and_write_for_all_sons_body_inside_seq rest param firstRes


and _find_read_and_write_for_all_sons_body_  body param retList = match body with
| Const'(x) -> retList
| Var'(x) -> retList
| If'(x, y, z)->  let l1 = (_find_read_and_write_for_all_sons_body_ x param retList) in
                  let l2 = (_find_read_and_write_for_all_sons_body_ y param l1) in
                  _find_read_and_write_for_all_sons_body_ z param l2 
| Seq'(x) -> _find_read_and_write_for_all_sons_body_inside_seq x param retList
| Set'(x, y) -> _find_read_and_write_for_all_sons_body_ y param retList
| Def'(x, y) -> _find_read_and_write_for_all_sons_body_ y param retList
| Or'(x) ->  _find_read_and_write_for_all_sons_body_inside_seq x param retList
| LambdaSimple'(pram,body) as l -> (_find_read_and_write_for_sub_trees_ l param [false; false])  :: retList
| LambdaOpt'(pram, variadic, body) as l -> (_find_read_and_write_for_sub_trees_ l param [false; false])  :: retList
| Applic'(x, y) ->  let l1 = _find_read_and_write_for_all_sons_body_ x param retList in
                    _find_read_and_write_for_all_sons_body_inside_seq y param l1
| ApplicTP'(x, y) -> let l1 = _find_read_and_write_for_all_sons_body_ x param retList in
                    _find_read_and_write_for_all_sons_body_inside_seq y param l1
| BoxSet'(x,e) -> (_find_read_and_write_for_all_sons_body_ e param retList) (* think about the senerio when x is param*)
| _ -> retList


and  _find_read_and_write_for_sub_trees_seq_ exprList p res = match exprList with
| [] -> res
| first::rest -> let firstRes = _find_read_and_write_for_sub_trees_ first p res in
                _find_read_and_write_for_sub_trees_seq_ rest p firstRes




and _find_read_and_write_for_sub_trees_ lambda p res = match lambda with 
| LambdaSimple'(pram,body) when  (List.mem  p pram)-> res
| LambdaOpt'(pram, variadic, body) when ((List.mem p pram) || (variadic = p)) -> res
| LambdaSimple'(pram,body) -> _find_read_and_write_for_sub_trees_ body p res
| LambdaOpt'(pram, variadic, body) ->  _find_read_and_write_for_sub_trees_ body p res
| Const'(x) -> res
| Var'(VarParam(name, i)) -> res
| Var'(VarBound(name, i, j)) -> if name = p then [true; (List.nth res 1) ] else res
| Var'(VarFree(name)) -> res
| If'(x, y, z)->  let res1 = (_find_read_and_write_for_sub_trees_ x p res) in
                  let res2 = (_find_read_and_write_for_sub_trees_ y p res1) in
                  (_find_read_and_write_for_sub_trees_ z p res2)              
| Seq'(x) -> _find_read_and_write_for_sub_trees_seq_ x p res
| Set'( Var'(VarParam(name, i)) , y) -> _find_read_and_write_for_sub_trees_ y p res
| Set'(Var'(VarBound(name, i, j)) , y) -> if name = p  
                                          then (_find_read_and_write_for_sub_trees_ y p  [(List.nth res 0);true]) 
                                          else (_find_read_and_write_for_sub_trees_ y p res)
| Set'(Var'(VarFree(name)), y) ->  _find_read_and_write_for_sub_trees_ y p res
| Def'(x, y) -> _find_read_and_write_for_sub_trees_ y p res
| Or'(x) ->  _find_read_and_write_for_sub_trees_seq_ x p res
| Applic'(x, y) ->  let res1 = _find_read_and_write_for_sub_trees_ x p res in
                               _find_read_and_write_for_sub_trees_seq_ y p res1
| ApplicTP'(x, y) ->  let res1 = _find_read_and_write_for_sub_trees_ x p res in
                      _find_read_and_write_for_sub_trees_seq_ y p res1
| BoxSet'(x,e) ->  _find_read_and_write_for_sub_trees_ e p res (* think about the senerio when x is param*)
| _ -> res;;

let _find_read_and_write_for_all_sons_ parentLambda param = match parentLambda with
| LambdaSimple'(params,body)-> _find_read_and_write_for_all_sons_body_ body param []
| LambdaOpt'(params, variadic, body) -> _find_read_and_write_for_all_sons_body_ body param []
| _ -> failwith " is_x_pram_in_lambda witout lambda";;


 let rec rec_is_box_nedded_ list = match list with 
| [false;false]::rest -> rec_is_box_nedded_  rest
| [true;true]::rest ->  find_true rest
| [false;true]::rest ->  find_left_true rest
| [true;false]::rest ->  find_right_true rest
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

and find_true list = match list with 
| [false;false]::rest -> find_true  rest
| [true;true]::rest ->  true
| [false;true]::rest ->  true
| [true;false]::rest ->  true
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

and find_left_true list = match list with 
| [false;false]::rest -> find_left_true  rest
| [true;true]::rest ->  true
| [false;true]::rest ->  find_left_true rest
| [true;false]::rest ->  true
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

and find_right_true list = match list with 
| [false;false]::rest -> find_right_true  rest
| [true;true]::rest ->  true
| [false;true]::rest ->  true
| [true;false]::rest ->  find_right_true rest
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

let rec _box_set_get_ p body = match body with
| LambdaSimple'(params,body) when  (List.mem p params)-> body
| LambdaOpt'(params, variadic, body) when ((List.mem p params) || (variadic = p)) -> body
| LambdaSimple'(pram,body) ->  LambdaSimple'(pram, _box_set_get_ p body)
| LambdaOpt'(pram, variadic, body) -> LambdaOpt'(pram, variadic,( _box_set_get_ p body) )
| Const'(x) -> body
| Var'(VarParam(name, i)) -> if (name = p) then BoxGet'(VarParam(name, i)) else body 
| Var'(VarBound(name, i, j)) -> if (name = p) then BoxGet'(VarBound(name, i, j)) else body
| Var'(VarFree(name)) -> body
| If'(x, y, z)->  If'(_box_set_get_ p x, _box_set_get_ p y, _box_set_get_ p z)              
| Seq'(x) -> Seq'(List.map (_box_set_get_ p) x)
| Set'(Var'(VarParam(name, i)) , y) ->  if name = p  
                                        then (BoxSet'(VarParam(name, i) , (_box_set_get_ p y))) 
                                        else Set'(Var'(VarParam(name, i)) , (_box_set_get_ p y))
| Set'(Var'(VarBound(name, i, j)) , y) -> if name = p  
                                          then (BoxSet'(VarBound(name, i, j) , (_box_set_get_ p y))) 
                                          else Set'(Var'(VarBound(name, i, j)) , (_box_set_get_ p y))
| Set'(Var'(VarFree(name)), y) ->  Set'(Var'(VarFree(name)), (_box_set_get_ p y))
| Def'(x, y) -> Def'(x, (_box_set_get_ p y))
| Or'(x) ->  Or'(List.map (_box_set_get_ p) x)
| Applic'(x, y) ->  Applic'((_box_set_get_ p x), (List.map (_box_set_get_ p) y))
| ApplicTP'(x, y) ->  ApplicTP'((_box_set_get_ p x), (List.map (_box_set_get_ p) y))
| Box'(x) ->  Box'(x)
| BoxGet'(x) -> BoxGet'(x)
| BoxSet'(x,e) ->  BoxSet'(x,(_box_set_get_ p e))
| _ -> failwith "wrong type for _box_set_get_";;

let _box_function_ parentLambda param minor = match parentLambda with
| LambdaSimple'(pram,body) -> LambdaSimple'(pram,Seq'([Set'(Var'(VarParam(param,minor)),Box'(VarParam(param, minor)))
; _box_set_get_ param body]))
| LambdaOpt'(pram, variadic, body) -> LambdaOpt'(pram, variadic, Seq'([Set'(Var'(VarParam(param,minor)),Box'(VarParam(param, minor)))
; _box_set_get_ param body]))
| _ ->  failwith "failwith _box_function_";;

 

let find_read_and_write_lambda_and_sons parentLambda param minor= let readWrite = find_read_and_write_only_in_body parentLambda param in
                                                                      let readWriteInside = _find_read_and_write_for_all_sons_ parentLambda param in
                                                                      let allReadWrite =  readWrite @ readWriteInside in
                                                                      if (rec_is_box_nedded_ allReadWrite)
                                                                      then _box_function_ parentLambda param minor
                                                                      else parentLambda;;

let _lambda_params_ parentLambda = match parentLambda with
| LambdaSimple'(pram,body) -> pram
| LambdaOpt'(pram, variadic, body) -> pram @ [variadic]
| _ ->  failwith " _lambda_params_ fialwith";;
 

let rec _box_each_param_ parentLambda fixedParams minor = match fixedParams with
| [] -> parentLambda
| first::rest -> let tempRes = find_read_and_write_lambda_and_sons parentLambda first minor in
                _box_each_param_ tempRes rest (minor + 1);;


let find_read_and_write_lambda_and_sons_for_all_params parentLambda = let fixedParams = _lambda_params_ parentLambda in
                                                                      _box_each_param_ parentLambda fixedParams 0;;  




let rec rec_seq_is_set list param = match list with
| last::[] -> (is_set_body last param)
| first::rest -> if (is_set_body first param) then true else  (rec_seq_is_set rest param)
| [] -> false
                    
and is_set_body body param = match body with 
| Const'(x) -> false
| Var'(x) -> false
| If'(x, y, z)-> (is_set_body x param) || (is_set_body y param) || (is_set_body z param)
| Seq'(x) -> (rec_seq_is_set x param)
| Set'(Var'(VarFree(x)), y) -> false 
| Set'(Var'(VarParam(name, i)), y) -> if name = param then true else false
| Set'(Var'(VarBound(name, i, j)), y) -> if name = param then true else false 
| Def'(x, y) -> false
| Or'(x) -> (rec_seq_is_set x param)
| LambdaSimple'(pram,body) -> false
| LambdaOpt'(pram, variadic, body) -> false
| Applic'(x, y) ->  (is_set_body x param) || (rec_seq_is_set y param)
| ApplicTP'(x, y) ->  (is_set_body x param) || (rec_seq_is_set y param)
| BoxSet'(x,e) -> (is_set_body e param) (* think about the senerio when x is param*)
| _ -> false


and is_set lambda param = match lambda with 
| LambdaSimple'(pram,body) -> (is_set_body body param)
| LambdaOpt'(pram, variadic, body) -> (is_set_body body param)
| _ -> failwith " is_set witout lambda";;


let rec rec_seq_is_read list param = match list with
| last::[] -> (is_read_body last param)
| first::rest -> if (is_read_body first param) then true else  (rec_seq_is_read rest param)
| [] -> false
                    
and is_read_body body param = match body with 
| Const'(x) -> false
| Var'(VarParam(name, i)) -> if name = param then true else false
| Var'(VarBound(name, i, j)) -> if name = param then true else false
| If'(x, y, z)-> (is_read_body x param) || (is_read_body y param) || (is_read_body z param)
| Seq'(x) -> (rec_seq_is_read x param)
| Set'(x, y) -> is_read_body y param
| Def'(x, y) -> false
| Or'(x) -> (rec_seq_is_read x param)
| LambdaSimple'(pram,body) -> false
| LambdaOpt'(pram, variadic, body) -> false
| Applic'(x, y) ->  (is_read_body x param) || (rec_seq_is_read y param)
| ApplicTP'(x, y) ->  (is_read_body x param) || (rec_seq_is_read y param)
| BoxSet'(x,e) -> (is_read_body e param) (* think about the senerio when x is param*)
| _ -> false


and is_read lambda param = match lambda with 
| LambdaSimple'(prams,body) -> (is_read_body body param)
| LambdaOpt'(prams, variadic, body) -> (is_read_body body param)
| _ -> failwith " is_read witout lambda";;

(* ****************************************8 *)


let is_x_pram_in_lambda l x = match l with 
| LambdaSimple'(prams,body) -> List.mem x prams 
| LambdaOpt'(prams, variadic, body) -> List.mem x prams || x = variadic
| _ -> failwith " is_x_pram_in_lambda witout lambda";;

let find_read_and_write_only_in_body parentLambda param = let read = is_read parentLambda param in
                                                          let write = is_set parentLambda param in
                                                          [[read ; write]];;

let  rec _find_read_and_write_for_all_sons_body_inside_seq exprList param retList = match exprList with
| [] -> retList
| first::rest -> let firstRes = _find_read_and_write_for_all_sons_body_ first param retList in
                _find_read_and_write_for_all_sons_body_inside_seq rest param firstRes


and _find_read_and_write_for_all_sons_body_  body param retList = match body with
| Const'(x) -> retList
| Var'(x) -> retList
| If'(x, y, z)->  let l1 = (_find_read_and_write_for_all_sons_body_ x param retList) in
                  let l2 = (_find_read_and_write_for_all_sons_body_ y param l1) in
                  _find_read_and_write_for_all_sons_body_ z param l2 
| Seq'(x) -> _find_read_and_write_for_all_sons_body_inside_seq x param retList
| Set'(x, y) -> _find_read_and_write_for_all_sons_body_ y param retList
| Def'(x, y) -> _find_read_and_write_for_all_sons_body_ y param retList
| Or'(x) ->  _find_read_and_write_for_all_sons_body_inside_seq x param retList
| LambdaSimple'(pram,body) as l -> (_find_read_and_write_for_sub_trees_ l param [false; false])  :: retList
| LambdaOpt'(pram, variadic, body) as l -> (_find_read_and_write_for_sub_trees_ l param [false; false])  :: retList
| Applic'(x, y) ->  let l1 = _find_read_and_write_for_all_sons_body_ x param retList in
                    _find_read_and_write_for_all_sons_body_inside_seq y param l1
| ApplicTP'(x, y) -> let l1 = _find_read_and_write_for_all_sons_body_ x param retList in
                    _find_read_and_write_for_all_sons_body_inside_seq y param l1
| BoxSet'(x,e) -> (_find_read_and_write_for_all_sons_body_ e param retList) (* think about the senerio when x is param*)
| _ -> retList


and  _find_read_and_write_for_sub_trees_seq_ exprList p res = match exprList with
| [] -> res
| first::rest -> let firstRes = _find_read_and_write_for_sub_trees_ first p res in
                _find_read_and_write_for_sub_trees_seq_ rest p firstRes




and _find_read_and_write_for_sub_trees_ lambda p res = match lambda with 
| LambdaSimple'(pram,body) when  (List.mem  p pram)-> res
| LambdaOpt'(pram, variadic, body) when ((List.mem p pram) || (variadic = p)) -> res
| LambdaSimple'(pram,body) -> _find_read_and_write_for_sub_trees_ body p res
| LambdaOpt'(pram, variadic, body) ->  _find_read_and_write_for_sub_trees_ body p res
| Const'(x) -> res
| Var'(VarParam(name, i)) -> res
| Var'(VarBound(name, i, j)) -> if name = p then [true; (List.nth res 1) ] else res
| Var'(VarFree(name)) -> res
| If'(x, y, z)->  let res1 = (_find_read_and_write_for_sub_trees_ x p res) in
                  let res2 = (_find_read_and_write_for_sub_trees_ y p res1) in
                  (_find_read_and_write_for_sub_trees_ z p res2)              
| Seq'(x) -> _find_read_and_write_for_sub_trees_seq_ x p res
| Set'( Var'(VarParam(name, i)) , y) -> _find_read_and_write_for_sub_trees_ y p res
| Set'(Var'(VarBound(name, i, j)) , y) -> if name = p  
                                          then (_find_read_and_write_for_sub_trees_ y p  [(List.nth res 0);true]) 
                                          else (_find_read_and_write_for_sub_trees_ y p res)
| Set'(Var'(VarFree(name)), y) ->  _find_read_and_write_for_sub_trees_ y p res
| Def'(x, y) -> _find_read_and_write_for_sub_trees_ y p res
| Or'(x) ->  _find_read_and_write_for_sub_trees_seq_ x p res
| Applic'(x, y) ->  let res1 = _find_read_and_write_for_sub_trees_ x p res in
                               _find_read_and_write_for_sub_trees_seq_ y p res1
| ApplicTP'(x, y) ->  let res1 = _find_read_and_write_for_sub_trees_ x p res in
                      _find_read_and_write_for_sub_trees_seq_ y p res1
| BoxSet'(x,e) ->  _find_read_and_write_for_sub_trees_ e p res (* think about the senerio when x is param*)
| _ -> res;;

let _find_read_and_write_for_all_sons_ parentLambda param = match parentLambda with
| LambdaSimple'(params,body)-> _find_read_and_write_for_all_sons_body_ body param []
| LambdaOpt'(params, variadic, body) -> _find_read_and_write_for_all_sons_body_ body param []
| _ -> failwith " is_x_pram_in_lambda witout lambda";;


 let rec rec_is_box_nedded_ list = match list with 
| [false;false]::rest -> rec_is_box_nedded_  rest
| [true;true]::rest ->  find_true rest
| [false;true]::rest ->  find_left_true rest
| [true;false]::rest ->  find_right_true rest
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

and find_true list = match list with 
| [false;false]::rest -> find_true  rest
| [true;true]::rest ->  true
| [false;true]::rest ->  true
| [true;false]::rest ->  true
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

and find_left_true list = match list with 
| [false;false]::rest -> find_left_true  rest
| [true;true]::rest ->  true
| [false;true]::rest ->  find_left_true rest
| [true;false]::rest ->  true
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

and find_right_true list = match list with 
| [false;false]::rest -> find_right_true  rest
| [true;true]::rest ->  true
| [false;true]::rest ->  true
| [true;false]::rest ->  find_right_true rest
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

let rec _box_set_get_ p body = match body with
| LambdaSimple'(params,body) when  (List.mem p params)-> body
| LambdaOpt'(params, variadic, body) when ((List.mem p params) || (variadic = p)) -> body
| LambdaSimple'(pram,body) ->  LambdaSimple'(pram, _box_set_get_ p body)
| LambdaOpt'(pram, variadic, body) -> LambdaOpt'(pram, variadic,( _box_set_get_ p body) )
| Const'(x) -> body
| Var'(VarParam(name, i)) -> if (name = p) then BoxGet'(VarParam(name, i)) else body 
| Var'(VarBound(name, i, j)) -> if (name = p) then BoxGet'(VarBound(name, i, j)) else body
| Var'(VarFree(name)) -> body
| If'(x, y, z)->  If'(_box_set_get_ p x, _box_set_get_ p y, _box_set_get_ p z)              
| Seq'(x) -> Seq'(List.map (_box_set_get_ p) x)
| Set'(Var'(VarParam(name, i)) , y) ->  if name = p  
                                        then (BoxSet'(VarParam(name, i) , (_box_set_get_ p y))) 
                                        else Set'(Var'(VarParam(name, i)) , (_box_set_get_ p y))
| Set'(Var'(VarBound(name, i, j)) , y) -> if name = p  
                                          then (BoxSet'(VarBound(name, i, j) , (_box_set_get_ p y))) 
                                          else Set'(Var'(VarBound(name, i, j)) , (_box_set_get_ p y))
| Set'(Var'(VarFree(name)), y) ->  Set'(Var'(VarFree(name)), (_box_set_get_ p y))
| Def'(x, y) -> Def'(x, (_box_set_get_ p y))
| Or'(x) ->  Or'(List.map (_box_set_get_ p) x)
| Applic'(x, y) ->  Applic'((_box_set_get_ p x), (List.map (_box_set_get_ p) y))
| ApplicTP'(x, y) ->  ApplicTP'((_box_set_get_ p x), (List.map (_box_set_get_ p) y))
| Box'(x) ->  Box'(x)
| BoxGet'(x) -> BoxGet'(x)
| BoxSet'(x,e) ->  BoxSet'(x,(_box_set_get_ p e))
| _ -> failwith "wrong type for _box_set_get_";;

let _box_function_ parentLambda param minor = match parentLambda with
| LambdaSimple'(pram,body) -> LambdaSimple'(pram,Seq'([Set'(Var'(VarParam(param,minor)),Box'(VarParam(param, minor)))
; _box_set_get_ param body]))
| LambdaOpt'(pram, variadic, body) -> LambdaOpt'(pram, variadic, Seq'([Set'(Var'(VarParam(param,minor)),Box'(VarParam(param, minor)))
; _box_set_get_ param body]))
| _ -> failwith "wrong type _box_function_";;

 

let find_read_and_write_lambda_and_sons parentLambda param minor= let readWrite = find_read_and_write_only_in_body parentLambda param in
                                                                      let readWriteInside = _find_read_and_write_for_all_sons_ parentLambda param in
                                                                      let allReadWrite =  readWrite @ readWriteInside in
                                                                      if (rec_is_box_nedded_ allReadWrite)
                                                                      then _box_function_ parentLambda param minor
                                                                      else parentLambda;;

let _lambda_params_ parentLambda = match parentLambda with
| LambdaSimple'(pram,body) -> pram
| LambdaOpt'(pram, variadic, body) -> pram @ [variadic]
| _ -> failwith "_lambda_params_ failwith";;


let rec _box_each_param_ parentLambda fixedParams minor = match fixedParams with
| [] -> parentLambda
| first::rest -> let tempRes = find_read_and_write_lambda_and_sons parentLambda first minor in
                _box_each_param_ tempRes rest (minor + 1);;


let find_read_and_write_lambda_and_sons_for_all_params parentLambda = let fixedParams = _lambda_params_ parentLambda in
                                                                      _box_each_param_ parentLambda fixedParams 0;;  
let rec rec_seq_is_set list param = match list with
| last::[] -> (is_set_body last param)
| first::rest -> if (is_set_body first param) then true else  (rec_seq_is_set rest param)
| [] -> false
                    
and is_set_body body param = match body with 
| Const'(x) -> false
| Var'(x) -> false
| If'(x, y, z)-> (is_set_body x param) || (is_set_body y param) || (is_set_body z param)
| Seq'(x) -> (rec_seq_is_set x param)
| Set'(Var'(VarFree(x)), y) -> false 
| Set'(Var'(VarParam(name, i)), y) -> if name = param then true else false
| Set'(Var'(VarBound(name, i, j)), y) -> if name = param then true else false 
| Def'(x, y) -> false
| Or'(x) -> (rec_seq_is_set x param)
| LambdaSimple'(pram,body) -> false
| LambdaOpt'(pram, variadic, body) -> false
| Applic'(x, y) ->  (is_set_body x param) || (rec_seq_is_set y param)
| ApplicTP'(x, y) ->  (is_set_body x param) || (rec_seq_is_set y param)
| BoxSet'(x,e) -> (is_set_body e param) (* think about the senerio when x is param*)
| _ -> false


and is_set lambda param = match lambda with 
| LambdaSimple'(pram,body) -> (is_set_body body param)
| LambdaOpt'(pram, variadic, body) -> (is_set_body body param)
| _ -> failwith " is_set witout lambda";;


let rec rec_seq_is_read list param = match list with
| last::[] -> (is_read_body last param)
| first::rest -> if (is_read_body first param) then true else  (rec_seq_is_read rest param)
| [] -> false
                    
and is_read_body body param = match body with 
| Const'(x) -> false
| Var'(VarParam(name, i)) -> if name = param then true else false
| Var'(VarBound(name, i, j)) -> if name = param then true else false
| If'(x, y, z)-> (is_read_body x param) || (is_read_body y param) || (is_read_body z param)
| Seq'(x) -> (rec_seq_is_read x param)
| Set'(x, y) -> is_read_body y param
| Def'(x, y) -> false
| Or'(x) -> (rec_seq_is_read x param)
| LambdaSimple'(pram,body) -> false
| LambdaOpt'(pram, variadic, body) -> false
| Applic'(x, y) ->  (is_read_body x param) || (rec_seq_is_read y param)
| ApplicTP'(x, y) ->  (is_read_body x param) || (rec_seq_is_read y param)
| BoxSet'(x,e) -> (is_read_body e param) (* think about the senerio when x is param*)
| _ -> false


and is_read lambda param = match lambda with 
| LambdaSimple'(prams,body) -> (is_read_body body param)
| LambdaOpt'(prams, variadic, body) -> (is_read_body body param)
| _ -> failwith " is_read witout lambda";;

(* ****************************************8 *)


let is_x_pram_in_lambda l x = match l with 
| LambdaSimple'(prams,body) -> List.mem x prams 
| LambdaOpt'(prams, variadic, body) -> List.mem x prams || x = variadic
| _ -> failwith " is_x_pram_in_lambda witout lambda";;


let find_read_and_write_only_in_body parentLambda param = let read = is_read parentLambda param in
                                                          let write = is_set parentLambda param in
                                                          [[read ; write]];;

let  rec _find_read_and_write_for_all_sons_body_inside_seq exprList param retList = match exprList with
| [] -> retList
| first::rest -> let firstRes = _find_read_and_write_for_all_sons_body_ first param retList in
                _find_read_and_write_for_all_sons_body_inside_seq rest param firstRes


and _find_read_and_write_for_all_sons_body_  body param retList = match body with
| Const'(x) -> retList
| Var'(x) -> retList
| If'(x, y, z)->  let l1 = (_find_read_and_write_for_all_sons_body_ x param retList) in
                  let l2 = (_find_read_and_write_for_all_sons_body_ y param l1) in
                  _find_read_and_write_for_all_sons_body_ z param l2 
| Seq'(x) -> _find_read_and_write_for_all_sons_body_inside_seq x param retList
| Set'(x, y) -> _find_read_and_write_for_all_sons_body_ y param retList
| Def'(x, y) -> _find_read_and_write_for_all_sons_body_ y param retList
| Or'(x) ->  _find_read_and_write_for_all_sons_body_inside_seq x param retList
| LambdaSimple'(pram,body) as l -> (_find_read_and_write_for_sub_trees_ l param [false; false])  :: retList
| LambdaOpt'(pram, variadic, body) as l -> (_find_read_and_write_for_sub_trees_ l param [false; false])  :: retList
| Applic'(x, y) ->  let l1 = _find_read_and_write_for_all_sons_body_ x param retList in
                    _find_read_and_write_for_all_sons_body_inside_seq y param l1
| ApplicTP'(x, y) -> let l1 = _find_read_and_write_for_all_sons_body_ x param retList in
                    _find_read_and_write_for_all_sons_body_inside_seq y param l1
| BoxSet'(x,e) -> (_find_read_and_write_for_all_sons_body_ e param retList) (* think about the senerio when x is param*)
| _ -> retList


and  _find_read_and_write_for_sub_trees_seq_ exprList p res = match exprList with
| [] -> res
| first::rest -> let firstRes = _find_read_and_write_for_sub_trees_ first p res in
                _find_read_and_write_for_sub_trees_seq_ rest p firstRes




and _find_read_and_write_for_sub_trees_ lambda p res = match lambda with 
| LambdaSimple'(pram,body) when  (List.mem  p pram)-> res
| LambdaOpt'(pram, variadic, body) when ((List.mem p pram) || (variadic = p)) -> res
| LambdaSimple'(pram,body) -> _find_read_and_write_for_sub_trees_ body p res
| LambdaOpt'(pram, variadic, body) ->  _find_read_and_write_for_sub_trees_ body p res
| Const'(x) -> res
| Var'(VarParam(name, i)) -> res
| Var'(VarBound(name, i, j)) -> if name = p then [true; (List.nth res 1) ] else res
| Var'(VarFree(name)) -> res
| If'(x, y, z)->  let res1 = (_find_read_and_write_for_sub_trees_ x p res) in
                  let res2 = (_find_read_and_write_for_sub_trees_ y p res1) in
                  (_find_read_and_write_for_sub_trees_ z p res2)              
| Seq'(x) -> _find_read_and_write_for_sub_trees_seq_ x p res
| Set'( Var'(VarParam(name, i)) , y) -> _find_read_and_write_for_sub_trees_ y p res
| Set'(Var'(VarBound(name, i, j)) , y) -> if name = p  
                                          then (_find_read_and_write_for_sub_trees_ y p  [(List.nth res 0);true]) 
                                          else (_find_read_and_write_for_sub_trees_ y p res)
| Set'(Var'(VarFree(name)), y) ->  _find_read_and_write_for_sub_trees_ y p res
| Def'(x, y) -> _find_read_and_write_for_sub_trees_ y p res
| Or'(x) ->  _find_read_and_write_for_sub_trees_seq_ x p res
| Applic'(x, y) ->  let res1 = _find_read_and_write_for_sub_trees_ x p res in
                                _find_read_and_write_for_sub_trees_seq_ y p res1
| ApplicTP'(x, y) ->  let res1 = _find_read_and_write_for_sub_trees_ x p res in
                      _find_read_and_write_for_sub_trees_seq_ y p res1
| BoxSet'(x,e) ->  _find_read_and_write_for_sub_trees_ e p res (* think about the senerio when x is param*)
| _ -> res;;

let _find_read_and_write_for_all_sons_ parentLambda param = match parentLambda with
| LambdaSimple'(params,body)-> _find_read_and_write_for_all_sons_body_ body param []
| LambdaOpt'(params, variadic, body) -> _find_read_and_write_for_all_sons_body_ body param []
| _ -> failwith " is_x_pram_in_lambda witout lambda";;


  let rec rec_is_box_nedded_ list = match list with 
| [false;false]::rest -> rec_is_box_nedded_  rest
| [true;true]::rest ->  find_true rest
| [false;true]::rest ->  find_left_true rest
| [true;false]::rest ->  find_right_true rest
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

and find_true list = match list with 
| [false;false]::rest -> find_true  rest
| [true;true]::rest ->  true
| [false;true]::rest ->  true
| [true;false]::rest ->  true
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

and find_left_true list = match list with 
| [false;false]::rest -> find_left_true  rest
| [true;true]::rest ->  true
| [false;true]::rest ->  find_left_true rest
| [true;false]::rest ->  true
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

and find_right_true list = match list with 
| [false;false]::rest -> find_right_true  rest
| [true;true]::rest ->  true
| [false;true]::rest ->  true
| [true;false]::rest ->  find_right_true rest
| [] -> false
| _ -> failwith "rec_is_box_nedded_ got bad input" 

let rec _box_set_get_ p body = match body with
| LambdaSimple'(params,_body) when  (List.mem p params)-> body
| LambdaOpt'(params, variadic, _body) when ((List.mem p params) || (variadic = p)) -> body
| LambdaSimple'(pram , _body) ->  LambdaSimple'(pram, _box_set_get_ p _body)
| LambdaOpt'(pram, variadic, _body) -> LambdaOpt'(pram, variadic,( _box_set_get_ p _body) )
| Const'(x) -> body
| Var'(VarParam(name, i)) -> if (name = p) then BoxGet'(VarParam(name, i)) else body 
| Var'(VarBound(name, i, j)) -> if (name = p) then BoxGet'(VarBound(name, i, j)) else body
| Var'(VarFree(name)) -> body
| If'(x, y, z)->  If'(_box_set_get_ p x, _box_set_get_ p y, _box_set_get_ p z)              
| Seq'(x) -> Seq'(List.map (_box_set_get_ p) x)
| Set'(Var'(VarParam(name, i)) , y) ->  if name = p  
                                        then (BoxSet'(VarParam(name, i) , (_box_set_get_ p y))) 
                                        else Set'(Var'(VarParam(name, i)) , (_box_set_get_ p y))
| Set'(Var'(VarBound(name, i, j)) , y) -> if name = p  
                                          then (BoxSet'(VarBound(name, i, j) , (_box_set_get_ p y))) 
                                          else Set'(Var'(VarBound(name, i, j)) , (_box_set_get_ p y))
| Set'(Var'(VarFree(name)), y) ->  Set'(Var'(VarFree(name)), (_box_set_get_ p y))
| Def'(x, y) -> Def'(x, (_box_set_get_ p y))
| Or'(x) ->  Or'(List.map (_box_set_get_ p) x)
| Applic'(x, y) ->  Applic'((_box_set_get_ p x), (List.map (_box_set_get_ p) y))
| ApplicTP'(x, y) ->  ApplicTP'((_box_set_get_ p x), (List.map (_box_set_get_ p) y))
| Box'(x) ->  Box'(x)
| BoxGet'(x) -> BoxGet'(x)
| BoxSet'(x,e) ->  BoxSet'(x,(_box_set_get_ p e))
| _ -> failwith "wrong type for _box_set_get_";;

let rec _box_set_get_on_last_ p _list = match _list with 
| body::[] -> (_box_set_get_ p body) :: []
| first :: rest -> first ::  (_box_set_get_on_last_ p rest )
| _ -> failwith "failwith _box_set_get_on_last_";;


let _box_function_ parentLambda param minor = match parentLambda with 

| LambdaSimple'(pram,  Seq'(Set'(a,Box'(b)) :: rest)) -> LambdaSimple'(pram,  Seq'( Set'(Var'(VarParam(param,minor)),Box'(VarParam(param, minor))) :: Set'(a,Box'(b)) ::(_box_set_get_on_last_ param rest))   )
| LambdaOpt'(pram, variadic,  Seq'(Set'(a,Box'(b)) :: rest)) -> LambdaOpt'(pram, variadic, Seq'( Set'(Var'(VarParam(param,minor)),Box'(VarParam(param, minor))) :: Set'(a,Box'(b)) :: (_box_set_get_on_last_ param rest))   )

| LambdaSimple'(pram,body) -> LambdaSimple'(pram,Seq'([Set'(Var'(VarParam(param,minor)),Box'(VarParam(param, minor)))
; _box_set_get_ param body]))
| LambdaOpt'(pram, variadic, body) -> LambdaOpt'(pram, variadic, Seq'([Set'(Var'(VarParam(param,minor)),Box'(VarParam(param, minor)))
; _box_set_get_ param body]))
| _ -> failwith "fail with _box_function_";;



let find_read_and_write_lambda_and_sons parentLambda param minor= let readWrite = find_read_and_write_only_in_body parentLambda param in
                                                                      let readWriteInside = _find_read_and_write_for_all_sons_ parentLambda param in
                                                                      let allReadWrite =  readWrite @ readWriteInside in
                                                                      if (rec_is_box_nedded_ allReadWrite)
                                                                      then _box_function_ parentLambda param minor 
                                                                      else parentLambda;;

let _lambda_params_ parentLambda = match parentLambda with
| LambdaSimple'(pram,body) -> pram
| LambdaOpt'(pram, variadic, body) -> pram @ [variadic]
| _ -> failwith "fail with_lambda_params_";;

let rec _box_each_param_ parentLambda fixedParams minor = match fixedParams with
| [] -> parentLambda
| first::rest -> let tempRes = find_read_and_write_lambda_and_sons parentLambda first minor in
                _box_each_param_ tempRes rest (minor - 1);;


let find_read_and_write_lambda_and_sons_for_all_params parentLambda = let fixedParams = _lambda_params_ parentLambda in
                                                                      _box_each_param_ parentLambda (List.rev fixedParams) ((List.length fixedParams)-1);;  
                                                                      
                                                                      


let rec box_set e = match e with 
| Const'(x) -> Const'(x)
| Var'(x) -> Var'(x)
| If'(x, y, z)-> If'(box_set x, box_set  y, box_set  z)
| Seq'(x) -> Seq'(List.map box_set x)
| Set'(x, y)-> Set'(box_set x, box_set y)
| Def'(x, y) -> Def'(box_set x, box_set y)
| Or'(x) -> Or'(List.map box_set x)
| LambdaSimple'(pram,body)-> find_read_and_write_lambda_and_sons_for_all_params (LambdaSimple'(pram,(box_set body)))
| LambdaOpt'(pram, variadic, body) -> find_read_and_write_lambda_and_sons_for_all_params (LambdaOpt'(pram,variadic,(box_set body)))
| Applic'(x, y) -> Applic' (box_set x, (List.map box_set y))
| ApplicTP'(x, y) -> ApplicTP' (box_set x, (List.map box_set y))
| _ -> failwith "box_set bad input"

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
