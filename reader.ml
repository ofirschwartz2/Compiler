
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
  | Vector(l1), Vector(l2) when (List.length l1) != (List.length l2) -> false
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
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



open PC;;

  let _boolean_ = let _false_ = pack(word_ci "#f")(fun a -> Bool (false)) in
  let _true_ = pack(word_ci "#t")( fun a -> Bool (true)) in
  let a = disj _true_ _false_ in
  pack a (fun a->a);;





let _digit_ = range '0' '9';;
let _digits_ = plus _digit_;;
let _plus_ = char '+';;
let _minus_ = char '-';;
let _dot_ = char '.';;
let _char_prefix_ = word_ci "#\\";;
let _symbol_char_ = disj_list [(range 'a' 'z');(range 'A' 'Z');(char_ci '!' );(char_ci '$');(char_ci '^');(char_ci '*');(char_ci '-');(char_ci '_');
                 (char_ci '=') ;(char_ci '+');(char_ci '<');(char_ci '>');(char_ci '/');(char_ci '?');(char_ci ':');_digit_]


let _symbol_ = let sym = plus _symbol_char_ in
 pack sym (fun x -> Symbol((  list_to_string( (List.map lowercase_ascii x)))));;





let _unsigned_int_ = let a = _digits_ in
       pack a (fun (a) -> int_of_string(list_to_string a));;

let _pos_int_ = let a = maybe _plus_ in
  let b = caten a _unsigned_int_ in
  pack b (fun(_,b) -> b);;

let _neg_int_ = let a = caten _minus_ _unsigned_int_ in
  pack a (fun(a,b) -> -1 * b);;

let _int_master_ = let a = not_followed_by (disj _pos_int_ _neg_int_) _symbol_ in
     pack a (fun(a) -> Number(Int(a)));;





let _unsigned_float_ = let a = caten _digits_ _dot_ in
         let b = caten a _digits_ in
         pack b (fun((a,b),c) ->float_of_string((list_to_string a) ^ "." ^ (list_to_string c)));;

let _pos_float_ = let a = maybe _plus_ in
    let b = caten a _unsigned_float_ in
    pack b (fun(a,b) -> b);;

let _neg_float_ = let a = caten _minus_ _unsigned_float_ in
    pack a (fun(a,b) -> -1.0 *. b);;

let _float_master_ = let a = disj _pos_float_ _neg_float_ in
       pack a (fun(a) -> Number(Float(a)));;





let _scientific_notation_ = let a = disj _neg_int_ _pos_int_ in
              let b = disj _neg_float_ _pos_float_ in
              let c = pack a (fun(a) -> float_of_int a) in
              let d = pack b (fun(a) -> a) in
              let e = disj d c in 
              let f = disj (char 'e') (char 'E') in
              let g = caten e f in
              let h = not_followed_by (caten g a) _symbol_ in 
              pack h (fun((a,b),c) -> Number(Float(10.0 ** (float_of_int c) *. a)));;





let _denoted_char_ = let _nul_ = pack (word_ci "nul") (fun x -> [(char_of_int 0)]) in
       let _newline_ =pack (word_ci "newline") (fun x -> [(char_of_int 10)]) in
       let _return_ = pack (word_ci "return") (fun x -> [(char_of_int 13)]) in
       let _tab_ = pack(word_ci "tab") (fun x -> [(char_of_int 9)]) in
       let _page_ = pack(word_ci "page") (fun x -> [(char_of_int 12)]) in
       let _space_ = pack(word_ci "space") (fun x -> [(char_of_int 32)]) in
       let d  =  disj_list [_nul_;_newline_;_return_;_tab_;_page_;_space_] in
       let e = caten _char_prefix_ d in
       let foo = function  |(a, [x])->Char(x)
                           | _ -> Char('d') in (* check if posssible to switch with exeption *)
       pack e foo;;

let _visible_chars_ = range (char_of_int 32) (char_of_int 127);;

let _visible_char_ = let a = caten _char_prefix_ _visible_chars_ in
       pack a (fun (a,b) -> Char(b)) ;;
       


let _hax_digit_ = disj_list [(range '0' '9');(range 'a' 'f');(range 'A' 'F' )];;
let _hax_number_ = plus _hax_digit_;;





let _hax_char_ = let  _x_ = char_ci 'x' in
   let _hax_char_prefix_ = caten _char_prefix_ _x_ in
   let c = caten _hax_char_prefix_ _hax_number_ in
   pack c (fun ((a,b),c) ->Char(char_of_int(int_of_string( "0x" ^ list_to_string(c)))));; (* handle the case of out of range hax  char *)
   

let _hax_digit_ = disj_list [(range '0' '9');(range 'a' 'f');(range 'A' 'F' )];;
let _hax_number_ = plus _hax_digit_;;

let _hax_num_pack_ = let c1 = caten (word_ci "#x") _hax_number_ in
       let c2 = caten (word_ci "#x+") _hax_number_ in
       let d = disj c1 c2 in
       pack d (fun (a,b) -> Number(Int(int_of_string("0x" ^ (list_to_string b)))));;


let _hax_num_pack_neg_ = let c = caten (word_ci "#x-") _hax_number_ in
           pack c (fun (a,b) -> Number(Int(-1 *  int_of_string("0x" ^ (list_to_string b)))));;


let _hax_num_float_ = let prefix = disj (word_ci "#x+") (word_ci "#x") in
        let c1 = caten prefix  _hax_number_ in
        let c2 = caten c1 _dot_ in
        let c3 = caten c2 _hax_number_ in
        pack c3 (fun (((a,b),c),d) -> Number(Float(float_of_string("0x" ^ (list_to_string b) ^ "." ^ (list_to_string d)))));;


let _hax_num_float_neg_ = let prefix = word_ci "#x-" in
            let c1 = caten prefix  _hax_number_ in
            let c2 = caten c1 _dot_ in
            let c3 = caten c2 _hax_number_ in
            pack c3 (fun (((a,b),c),d) -> Number(Float( float_of_string("-0x" ^ (list_to_string b) ^ "." ^ (list_to_string d)))));;






let _white_space_ =   pack (range (char_of_int 0) (char_of_int 32)) (fun x -> 1);;
let _white_spaces_ = pack (star(range (char_of_int 0) (char_of_int 32))) (fun x -> 1) ;;              
let _backslash_ = char (char_of_int 92);;
let _x_ = char 'x';;
let _semicolon_ = char ';';;


let _hex_digit_ = disj_list [(range '0' '9');(range 'a' 'f');(range 'A' 'F' )];;

let _string_hex_char_ = let a = disj (char 'x') (char 'X') in
          let b = caten _backslash_ a in
          let c = caten b (plus _hex_digit_) in
          let d = pack c (fun((a,b),c) -> ['0';'x']@c) in
          let e = caten d _semicolon_ in
          pack e (fun(a,b) -> char_of_int(int_of_string(list_to_string a)));;

let _string_meta_backslash_ = let a = caten _backslash_ _backslash_ in
                pack a (fun(a,b) -> char_of_int 92);;

let _string_meta_double_quote_ = let a = caten _backslash_ (char (char_of_int 34)) in
                pack a (fun(a,b) -> char_of_int 34);;

let _string_meta_page_ = let a = caten _backslash_ (char 'f') in
                pack a (fun(a,b) -> char_of_int 12);;

let _string_meta_tab_ = let a = caten _backslash_ (char 't') in
                pack a (fun(a,b) -> char_of_int 9);;

let _string_meta_newline_ = let a = caten _backslash_ (char 'n') in
                pack a (fun(a,b) -> char_of_int 10);;

let _string_meta_return_ = let a = caten _backslash_ (char 'r') in
                pack a (fun(a,b) -> char_of_int 13);;


let _string_meta_char_ = disj_list [_string_meta_backslash_;_string_meta_double_quote_;_string_meta_page_;_string_meta_tab_;_string_meta_newline_;_string_meta_return_];;

let _string_literal_char_ = const (fun (x) -> x !='\\' && x !='\"');;

let _string_char_ = disj_list [_string_hex_char_;_string_literal_char_;_string_meta_char_];;


let _string_ = let a = char (char_of_int 34) in
 let b = caten a (star _string_char_) in
 let c = pack b (fun(a,b) -> b) in
 let d = caten c (char (char_of_int 34)) in
 pack d (fun(a,b) -> String(list_to_string a));;let _hex_digit_ = disj_list [(range '0' '9');(range 'a' 'f');(range 'A' 'F' )];;



let  line_comments =  pack ( caten(   caten (char ';') (star (disj (range (char_of_int 0 ) (char_of_int 9)) (range (char_of_int 11 ) (char_of_int 128)))) ) (char '\n' )) (fun x -> 1) ;; (*validate the ranges*)  

let _white_spaces_and_line_comments_ = star (disj _white_space_ line_comments );;








(********       exp comments       ************)        

let rec parsers_list =[_scientific_notation_;_string_;vector ; _q_forms_ ;_hax_num_float_;_hax_num_float_neg_ ;_hax_num_pack_neg_ ;_hax_num_pack_;_hax_char_;_denoted_char_;
_visible_char_;_float_master_; _boolean_;_int_master_;_symbol_;_nil_;list; _3_dots_list_] 

and union_parser s =  disj_list parsers_list s


and _w_s_ s = let rec exp_comments s =  let c1 =  caten (caten _white_spaces_and_line_comments_ (word "#;")) exp_comments in
                          let c2 =  caten (caten c1  _white_spaces_and_line_comments_)   union_parser in
                          let c3 =  caten ( (caten _white_spaces_and_line_comments_ (caten (word "#;") _white_spaces_and_line_comments_ ))   ) union_parser in
                          let p3 =   pack (caten(caten c2 _white_spaces_and_line_comments_)   exp_comments ) (fun x -> 1) in
                          let p1 = pack c2 (fun x -> 1) in 
                          let p2 = pack c3 (fun x -> 1) in          
                          
                          disj_list [p2 ; p1 ; p3] s in
                          star (disj_list [  _white_space_  ;  exp_comments ; line_comments]) s

and _w_s_g_ s = let rec exp_comments s =  let c1 =  caten (caten _white_spaces_and_line_comments_ (word "#;")) exp_comments in
                            let c2 =  caten (caten c1  _white_spaces_and_line_comments_)   union_parser in
                            let c3 =  caten ( (caten _white_spaces_and_line_comments_ (caten (word "#;") _white_spaces_and_line_comments_ ))   ) union_parser in
                            let p3 =   pack (caten(caten c2 _white_spaces_and_line_comments_)   exp_comments ) (fun x -> 1) in
                            let p1 = pack c2 (fun x -> 1) in 
                            let p2 = pack c3 (fun x -> 1) in          

                            disj_list [p2 ; p1 ; p3] s in

  star (disj_list [  _white_space_  ;  exp_comments ; line_comments; (pack (word "...") (fun x-> 1) )]) s
                          
                      
and _w_s_p_ s = let rec exp_comments s =  let c1 =  caten (caten _white_spaces_and_line_comments_ (word "#;")) exp_comments in
                            
                            let c2 =  caten (caten c1  _white_spaces_and_line_comments_)   union_parser in
                            let c3 =  caten ( (caten _white_spaces_and_line_comments_ (caten (word "#;") _white_spaces_and_line_comments_ ))   ) union_parser in
                            let p3 =   pack (caten(caten c2 _white_spaces_and_line_comments_)   exp_comments ) (fun x -> 1) in
                            let p1 = pack c2 (fun x -> 1) in 
                            let p2 = pack c3 (fun x -> 1) in          
                            disj_list [p2 ; p1 ; p3] s in
                            plus (disj_list [  _white_space_  ;  exp_comments ; line_comments]) s



(***)
and _nil_ s = let d1 = caten (caten (char '(')  _w_s_) (char ')') in 
              let d2 = caten (caten (char '[')  _w_s_) (char ']') in
              
              pack (disj d1 d2) (fun x -> Nil) s


and list_dot_for_3_dot s =  let rec _rec_exp_1_ s = let d1 = pack (caten(caten(caten _w_s_     list_dot_for_3_dot   ) _w_s_) _rec_exp_1_)  (fun (((a,b),c),d)->  Pair(b , d)) in
                                                    let d2 = pack (caten(caten (caten _w_s_   union_parser  ) _w_s_ ) _rec_exp_1_) (fun (((a,b),c),d)-> Pair(b , d)) in
                                                    let e =   caten (caten (caten _w_s_ (char '.')) _w_s_) (disj union_parser  list_dot_for_3_dot) in
                                                    let d3 = pack e (fun (((a,b),c),d) -> d)   in 

                                                    disj_list [d1 ;d2 ; d3] s in

                                                    let e1 = pack (caten (caten _w_s_ (char '(')) _rec_exp_1_) (fun ((a,b),c) -> c) in 

                        

                                    let rec _rec_exp_2_ s = let d1 = pack (caten(caten(caten _w_s_     list_dot_for_3_dot   ) _w_s_) _rec_exp_1_)  (fun (((a,b),c),d)->  Pair(b , d)) in
                                    let d2 = pack (caten(caten (caten _w_s_   union_parser  ) _w_s_ ) _rec_exp_1_) (fun (((a,b),c),d)-> Pair(b , d)) in
                                    let e =   caten (caten (caten _w_s_ (char '.')) _w_s_) (disj union_parser  list_dot_for_3_dot) in
                                    let d3 = pack e (fun (((a,b),c),d) -> d)   in 

                                    disj_list [d1 ;d2 ; d3] s in

                                    let e2 = pack (caten (caten _w_s_ (char '[')) _rec_exp_1_) (fun ((a,b),c) -> c) in 

        

                                     disj e1 e2 s

                                    

(***)
(****)



and _q_forms_ s = let sym1 = pack (word "'") ( fun x -> Symbol("quote") )  in
    let sym2 = pack (word "`") ( fun x -> Symbol("quasiquote") )  in
    let sym3 = pack (word ",@") ( fun x -> Symbol("unquote-splicing") )  in
    let sym4 = pack (word ",") ( fun x -> Symbol("unquote") )  in

    pack (caten ( disj_list [sym1;sym2;sym3;sym4] ) union_parser ) (fun (a,b) -> Pair(a,Pair(b,Nil)) ) s 


and list s =  let rec _rec_exp_1_ s = let d1 = pack  (caten _w_s_ (char ')')) (fun x->Nil) in
                        let d2 = pack (caten(caten (caten _w_s_ union_parser) _w_s_ ) _rec_exp_1_) (fun (((a,b),c),d)-> Pair(b , d)) in
                        let e =  caten (caten (caten (caten (caten _w_s_ (char '.')) _w_s_) union_parser) _w_s_) (char ')')   in
                        let d3 = pack e (fun (((((a,b),c),d),e),f) -> d)   in 

                         disj_list [d1 ;d2 ;d3] s in
 
let e1 = pack (caten (caten _w_s_ (char '(')) _rec_exp_1_) (fun ((a,b),c) -> c) in 

let rec _rec_exp_2_ s = let d1 = pack  (caten _w_s_ (char ']')) (fun x->Nil) in
                        let d2 = pack (caten(caten (caten _w_s_ union_parser) _w_s_ ) _rec_exp_2_) (fun (((a,b),c),d)-> Pair(b , d)) in
                        let e =  caten (caten (caten (caten (caten _w_s_ (char '.')) _w_s_) union_parser) _w_s_) (char ']')   in
                        let d3 = pack e (fun (((((a,b),c),d),e),f) -> d)   in 
                        
                        disj_list [d1 ;d2 ;d3] s in
                  
let e2 = pack (caten (caten _w_s_ (char '[')) _rec_exp_2_) (fun ((a,b),c) -> c)  in 
  
disj e1 e2 s



and  vector s = let rec _rec_exp_ s =  let d1 = pack (caten(caten (caten _w_s_ union_parser) _w_s_) _rec_exp_  ) (fun (((a,b),c),d) -> b :: d ) in
                         let d2 = pack (caten _w_s_ (char ')')) (fun a -> []) in 
                         
                        disj d1 d2 s in
 
  pack (caten (word "#(") _rec_exp_) (fun (a,b) -> Vector(b) ) s
    

and _3_dots_list_ s = let parsers_list_3_  = [_scientific_notation_;_string_;vector ; _q_forms_ ;_hax_num_float_;_hax_num_float_neg_ ;_hax_num_pack_neg_ ;_hax_num_pack_;_hax_char_;_denoted_char_;
        _visible_char_;_float_master_; _boolean_;_int_master_;_symbol_;_nil_;list; list_dot_for_3_dot];  in
        let _union_parser_3_ =  disj_list parsers_list_3_ in
        let _open_list = disj (char '(') (char '[') in
        let _open_vec = word "#(" in
        let _close = word "..." in
        let _dot = char '.' in
        
        let rec rec_exp_list s = let p1 = pack  (caten(caten (caten (caten _w_s_ _dot ) _w_s_) _open_list)rec_exp_list) (fun ((((a ,b),c),d),e)-> e) in
                            let p2 = pack  (caten(caten(caten(caten(caten (caten (caten _w_s_  _union_parser_3_  ) _w_s_) _dot) _w_s_ ) _union_parser_3_) _w_s_ )_close) (fun (((((((a ,b),c),d),e),f),g),h)-> Pair(b,f)) in
                            let p3 = pack (caten (caten  _w_s_   _union_parser_3_) rec_exp_list )  (fun ((a,b),c) -> Pair(b,c)) in
                            let p4 = pack (caten (caten _w_s_  _open_list) rec_exp_list) (fun ((a,b),c) ->  Pair(c,Nil))  in
                            let p5 = pack (caten _w_s_  _close) (fun (a,b) ->  Nil)  in
          
                            disj_list [p1 ; p2 ; p3 ;p4 ;p5] s in

          pack (caten  _open_list rec_exp_list ) (fun (a,b) -> b) s ;;
          


  
let _union_parser_ = disj_list [_scientific_notation_;_string_;vector ; _q_forms_ ;_hax_num_float_;_hax_num_float_neg_ ;_hax_num_pack_neg_ ;_hax_num_pack_;_hax_char_;_denoted_char_;_visible_char_;_float_master_; _boolean_;_int_master_;_symbol_;_nil_;list; _3_dots_list_];;


                          
let read_sexpr string =fst( (pack (not_followed_by (caten(caten _w_s_  _union_parser_) _w_s_) _union_parser_)  (fun ((a,b),c) -> b)) (string_to_list string));;


let read_sexprs string = fst( (star(pack (caten(caten _w_s_g_  _union_parser_) _w_s_g_)   (fun ((a,b),c) -> b)) ) (string_to_list string));;


end;; (* struct Reader *)
