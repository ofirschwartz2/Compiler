#use "semantic-analyser.ml";;



module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * int * string) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * int * string) list -> (string * int) list -> expr' -> int -> string
end;;

module Code_Gen : CODE_GEN = struct
  let counter = ref 0;;



  let finishedList = [(Void, 0, "MAKE_VOID");
  (Sexpr(Nil), 1, "MAKE_NIL");
  (Sexpr(Bool false), 2, "MAKE_BOOL(0)");
  (Sexpr(Bool true), 4, "MAKE_BOOL(1)")];;

let rec expr'_to_const_table expr = match expr with 
| Const'(x) -> [x]
| If'(x, y, z)-> (expr'_to_const_table x) @ (expr'_to_const_table y) @ (expr'_to_const_table z) 
| Seq'(x) -> (List.flatten(List.map  expr'_to_const_table x))
| Set'(x, y) ->  (expr'_to_const_table y) 
| Def'(x, y) ->  (expr'_to_const_table y) 
| Or'(x) ->  (List.flatten(List.map  expr'_to_const_table x))
| LambdaSimple'(pram,body) -> (expr'_to_const_table body)
| LambdaOpt'(pram, variadic, body) -> (expr'_to_const_table body) 
| Applic'(x, y) -> (expr'_to_const_table x) @ (List.flatten(List.map  expr'_to_const_table y)) 
| ApplicTP'(x, y) -> (expr'_to_const_table x) @ (List.flatten(List.map  expr'_to_const_table y))
| BoxSet'(x,e) -> (expr'_to_const_table e) 
| _ -> [];;

  let add_if_not_mem list sexpr =   match sexpr with
  | Void -> list
  | Sexpr(s) -> if (List.exists (sexpr_eq s) list) then list else list @ [s];;

  let remove_dup list = let new_list = [Nil; Bool (false); Bool(true)] in
                      let ans = (List.fold_left add_if_not_mem new_list list) in
                      [Void] @ (List.map (fun x -> Sexpr(x)) ans);;

  let expers'_to_const_table expers = (List.flatten(List.map expr'_to_const_table expers));;


let rec extend_vector list = match list with
   | [] -> [] 
   | x :: rest -> (extend_expr x) @  (extend_vector rest) 
    
and add_sub_exprs list = match list with
   | [] -> []
   | Sexpr(x) :: rest -> (extend_expr x) @  (add_sub_exprs rest)
   | Void :: rest -> [Void] @ (add_sub_exprs rest )

and extend_expr expr = match expr with 
   | Symbol(s) -> [Sexpr(String(s)) ;  Sexpr(Symbol(s))]
   | Pair(a, b) -> (extend_expr a) @ (extend_expr b) @ [Sexpr(Pair(a, b))] 
   | Vector(v) -> if (v = []) then [Sexpr(Vector(v))]
                          else (extend_vector v) @ [Sexpr(Vector(v))]
   | _ -> [Sexpr(expr)];;

  let sizeOfRow sexpr = match sexpr with
   | Sexpr(Char(c)) -> 2
   | Sexpr(Bool(b)) -> 2
   | Void-> 1
   | Sexpr(Nil)-> 1
   | Sexpr(Number(Int(i))) -> 9
   | Sexpr(Number(Float(i))) -> 9
   | Sexpr(String(s)) -> (String.length s) + 9
   | Sexpr(Symbol(s)) -> 9
   | Sexpr(Vector(list)) -> ((List.length list) * 8 ) + 9
   | Sexpr(Pair(a, b)) -> 17;;

   let get_first (x,y,z) = x
   let get_second (x,y,z) = y
   let get_third (x,y,z) = z

   let rec find_adress_of const newList = match const with
   | Void -> "const_tbl"
   | Sexpr(sexpr) -> let first = (get_first(List.hd newList)) in
                     let address =  (get_second(List.hd newList))in
                     match first with
                     | Void -> (find_adress_of const (List.tl newList))
                     | Sexpr(s) -> if (sexpr_eq s sexpr) then "const_tbl + " ^  (string_of_int address)
                                  else (find_adress_of const (List.tl newList));;

  let find_adresses_of list newList = let f = fun acc e -> acc ^ (find_adress_of (Sexpr(e)) newList) ^ ", "  in
                                      let str_before_cut = (List.fold_left f "" list) in
                                      String.sub str_before_cut 0 ((String.length str_before_cut)-2);;

   let asmOfRow const newList = match const with
   | Sexpr(Char(c)) -> "MAKE_LITERAL_CHAR(" ^ (string_of_int (Char.code c)) ^ ")"
   | Sexpr(Bool(b)) -> if b then "MAKE_BOOL(1)"
                       else "MAKE_BOOL(0)"
   | Void -> "MAKE_VOID"
   | Sexpr(Nil) -> "MAKE_NIL"
   | Sexpr(Number(Int(i))) -> "MAKE_LITERAL_INT(" ^ (string_of_int i) ^ ")"
   | Sexpr(Number(Float(i))) -> "MAKE_LITERAL_FLOAT(" ^ (string_of_float i) ^ ")"
   | Sexpr(String(s)) -> "MAKE_LITERAL_STRING " ^ (String.concat ", " (List.map string_of_int (List.map Char.code  (string_to_list s)))) 
   | Sexpr(Symbol(s))  ->  "MAKE_LITERAL_SYMBOL(" ^ (find_adress_of (Sexpr(String(s))) newList) ^ ")"
   | Sexpr(Pair(a, b))  ->  "MAKE_LITERAL_PAIR(" ^  (find_adress_of (Sexpr(a)) newList) ^ "," ^ (find_adress_of (Sexpr(b)) newList) ^")"
   | Sexpr(Vector(list)) when list = [] -> "MAKE_LITERAL_VECTOR "
   | Sexpr(Vector(list)) -> "MAKE_LITERAL_VECTOR " ^ (find_adresses_of list newList ) ;;
   
   (asmOfRow (Sexpr(String("str"))) finishedList);;
             
   (sizeOfRow (Sexpr(String("str"))) );;

  let rec offsetFunc oldList offset newList =  if ((List.length oldList) = 0) then newList 
                                              else  let firstSize = (sizeOfRow (List.hd oldList)) in
                                                    let asmString = (asmOfRow (List.hd oldList) newList) in
                                                    (offsetFunc (List.tl oldList) (offset + firstSize)  (newList @ [((List.hd oldList), offset, asmString) ]));;

let rec find_adress_of_sexpr_in_const_list sexpr list = match list with 
| [] -> failwith "cant find cont in conts list"
| hd :: tl -> let sexper_to_check = (get_first hd) in
              let adress_to_return = (string_of_int (get_second hd)) in
              match sexper_to_check with
              |Void -> failwith "find_adress_of_sexpr_in_const_list get Void!!!"
              |Sexpr(s) -> if (sexpr_eq sexpr s) then  "const_tbl +" ^  adress_to_return
                           else  (find_adress_of_sexpr_in_const_list sexpr tl);;

let find_adress_in_const_list e consts = match e with
| Void -> "const_tbl"
| Sexpr(s)-> (find_adress_of_sexpr_in_const_list s (List.tl consts));;


let primitive_names_to_labels =  ["boolean?"; "float?"; "integer?"; "pair?";
   "null?" ; "char?"; "vector?"; "string?";
   "procedure?"; "symbol?" ; "string-length";
   "string-ref"; "string-set!"; "make-string";
   "vector-length"; "vector-ref"; "vector-set!";
   "make-vector"; "symbol->string"; 
   "char->integer"; "integer->char"; "eq?";
   "+"; "*"; "-"; "/"; "<"; "=";"cdr" ;  "car" ; "cons" ;"set-car!";"set-cdr!"; "apply" ];;
(*"car";"cdr"; "cons"]*)
let rec create_free_vars_table_expr' expr' = match expr' with
| Var'(VarFree(x)) -> [x] 
| BoxSet'(x,e) -> (create_free_vars_table_expr' e )
| If'(x, y, z)-> (create_free_vars_table_expr' x) @ (create_free_vars_table_expr' y) @ (create_free_vars_table_expr' z) 
| Seq'(x) -> (List.flatten(List.map  create_free_vars_table_expr' x))
| Set'(x, y) ->  (create_free_vars_table_expr' x) @ (create_free_vars_table_expr' y) 
| Def'(x, y) ->  (create_free_vars_table_expr' x) @ (create_free_vars_table_expr' y)
| Or'(x) ->  (List.flatten(List.map  create_free_vars_table_expr' x))
| LambdaSimple'(pram,body) -> (create_free_vars_table_expr' body)
| LambdaOpt'(pram, variadic, body) -> (create_free_vars_table_expr' body) 
| Applic'(x, y) -> (create_free_vars_table_expr' x) @ (List.flatten(List.map create_free_vars_table_expr' y)) 
| ApplicTP'(x, y) -> (create_free_vars_table_expr' x) @ (List.flatten(List.map create_free_vars_table_expr' y)) 
| _ -> [];;

let rec create_free_vars_table_exprs' exprs'_list  = match exprs'_list with
| [] -> []
| hd :: tl -> (create_free_vars_table_expr' hd )  @ (create_free_vars_table_exprs' tl );;

let rec remove_dup_in_string_list list new_list = match list with
| [] -> new_list
| hd :: tl -> if (List.mem hd new_list) then (remove_dup_in_string_list tl new_list) else (remove_dup_in_string_list tl (new_list @ [hd]));;

  let make_free_var_tbl_from_string_tbl list = List.mapi (fun x y -> (y, x)) list;;
  

  let make_consts_tbl asts = (offsetFunc (remove_dup (add_sub_exprs (remove_dup (expers'_to_const_table asts)))) 0 []) ;;
  
  let make_fvars_tbl asts = make_free_var_tbl_from_string_tbl (remove_dup_in_string_list (create_free_vars_table_exprs' asts) primitive_names_to_labels) ;;

  let crate_favr_label i = "[fvar_tbl + " ^ (string_of_int i) ^ " * WORD_BYTES]";;

  let rec find_label_in_fvars fvars v = match fvars with
  | [] -> failwith "find_label_in_fvars cant find v"
  | hd :: tl -> let var = (fst (List.hd fvars)) in
                let i = (snd (List.hd fvars)) in 
                if (v = var) then (crate_favr_label i)
                else (find_label_in_fvars tl v);;

  let rec handle_or_generate consts fvars list size_of_env = let label_num = (string_of_int counter.contents)  in
    match list with
| last :: [] -> (generate consts fvars last size_of_env) ^ "Lexit_" ^ label_num^ ":\n"
| hd :: tl -> (generate consts fvars hd size_of_env) ^ "cmp rax, SOB_FALSE_ADDRESS \njne Lexit_" ^ label_num^ "\n" ^ (handle_or_generate consts fvars tl size_of_env )
| [] -> "empty or should be allready hanled"

  and generate consts fvars e size_of_env =
  incr counter;
  let label_num = (string_of_int counter.contents)  in
  match e with
  | Const'(c) -> "mov rax," ^ (find_adress_in_const_list c consts) ^ "\n"
  | Var'(VarParam(_, minor)) -> "mov rax, qword [rbp + 8 * (4 +"  ^ (string_of_int minor) ^")] \n"
  | Var'(VarBound(_, major, minor)) -> "mov rax, qword [rbp + 8 * 2] " ^ "\n" ^ "mov rax, qword [rax + 8 * " ^ (string_of_int major) ^ "]" ^ "\n" ^  "mov rax, qword [rax + 8 * " ^ (string_of_int minor) ^ "] \n"
  | Set'(Var'(VarParam(_, minor)),ex) -> (generate consts fvars ex size_of_env) ^ "mov qword [rbp + 8 * (4 +" ^(string_of_int minor)^")], rax \n mov rax, sob_void \n"
  | Set'(Var'(VarBound(_,major,minor)),ex) -> (generate consts fvars ex size_of_env) ^ "mov rbx, qword [rbp + 8 * 2]"^ "\n" ^"mov rbx, qword [rbx + 8 * " ^ (string_of_int major) ^ "]" ^ "\n" ^ "mov qword [rbx + 8 * " ^ (string_of_int minor) ^ "], rax" ^ "\n" ^ "mov rax, sob_void \n"
  | Set'(Var'(VarFree(v)),ex) ->(generate consts fvars ex size_of_env) ^ "\nmov qword " ^ (find_label_in_fvars fvars v) ^ ", rax" ^ "\n" ^ "mov rax, SOB_VOID_ADDRESS\n"
  | Def'(Var'(VarFree(v)),ex) ->(generate consts fvars ex size_of_env) ^ "\nmov qword " ^ (find_label_in_fvars fvars v) ^ ", rax" ^ "\n" ^ "mov rax, SOB_VOID_ADDRESS\n"
  | Var'(VarFree(v))-> "mov rax, qword " ^ (find_label_in_fvars fvars v) ^ "\n"
  | Seq'(list) -> (List.fold_left (fun acc item -> acc ^ (generate consts fvars item size_of_env)) "" list)
  | Or'(x) ->  (handle_or_generate consts fvars x size_of_env)
  | If'(q,t, ex) -> (generate consts fvars q size_of_env) ^ "cmp rax, SOB_FALSE_ADDRESS\nje Lelse_" ^ label_num^ "\n" ^ (generate consts fvars t size_of_env) ^ "jmp Lexit_" ^ label_num^ "\nLelse_" ^ label_num^ ":\n" ^ (generate consts fvars ex size_of_env) ^ "Lexit_" ^ label_num^ ":\n"
  | BoxGet'(v) -> (generate consts fvars (Var'(v))size_of_env) ^ "mov rax, qword [rax]\n"
  | BoxSet'(v, e) -> (generate consts fvars e size_of_env) ^ "push rax\n" ^ (generate consts fvars (Var'(v)) size_of_env) ^ "pop qword [rax]\nmov rax, sob_void\n"
  | Box'(v) -> (generate consts fvars (Var'(v)) size_of_env) ^ "\nMALLOC r10, 8\n mov qword [r10], rax \nmov rax, r10\n"
  | LambdaSimple' (args_list , body) when (size_of_env = 0)->  ";;***labmdasimple (size_of_env = 0)*** \n" ^
                                                              "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode_" ^ label_num^ ")\n" ^
                                                              "jmp Lcont_" ^ label_num^ "\n" ^                                                            
                                                              "Lcode_" ^ label_num^ ":\n" ^
                                                              "push rbp\n" ^
                                                              "mov rbp , rsp\n" ^
                                                              (generate consts fvars body (size_of_env + 1) ) ^ "\n" ^
                                                              "leave\n" ^
                                                              "ret\n" ^
                                                              "Lcont_" ^ label_num ^ ":\n"

  | LambdaSimple' (args_list , body) -> ";;***labmdasimple*** \n" ^
                                        "\nMALLOC rbx, " ^ (string_of_int (size_of_env * 8) ) ^ "\n" ^
                                        "mov r8, " ^ (string_of_int size_of_env) ^ "\n" ^
                                        "cmp r8, 1\n" ^
                                        "JE AllocateExtEnv0_" ^ label_num^ "\n" ^           
                                        "mov rcx, 0\n" ^
                                        "mov rdx, qword [rbp + 8 * 2]\n\n" ^

                                        "EnvLoop_" ^ label_num^ ":\n" ^
                                        "mov rsi, qword [rdx + 8 * rcx]\n" ^
                                        "inc rcx\n" ^
                                        "mov qword [rbx + 8 * rcx], rsi\n" ^
                                        "cmp rcx, " ^ (string_of_int (size_of_env - 1)) ^ "\n" ^
                                        "JE AllocateExtEnv0_" ^ label_num^ "\n" ^
                                        "jmp EnvLoop_" ^ label_num^ "\n\n" ^
                                            
                                        "AllocateExtEnv0_" ^ label_num^ ":\n" ^
                                        "mov rcx, qword [rbp + 8 * 3]\n" ^
                                        "shl rcx, 3\n" ^
                                        "MALLOC rdx, rcx\n" ^
                                        "mov qword [rbx], rdx\n\n" ^

                                        "AllocateExtEnv0PerParam_" ^ label_num^ ":\n" ^
                                        "cmp rcx, 0\n" ^
                                        "JE MakeClosure_" ^ label_num^ "\n" ^
                                        "sub rcx, 8\n" ^
                                        "mov rsi, qword [rbp + (8 * 4) + rcx]\n" ^
                                        "mov qword [rdx + rcx], rsi\n" ^
                                        "jmp AllocateExtEnv0PerParam_" ^ label_num^ "\n\n" ^

                                        "MakeClosure_" ^ label_num^ ":\n" ^
                                        
                                        "MAKE_CLOSURE(rax, rbx, Lcode_" ^ label_num^ ")\n" ^
                                        "jmp Lcont_" ^ label_num^ "\n" ^
                                        "Lcode_" ^ label_num^ ":\n" ^
                                        "push rbp\n" ^
                                        "mov rbp , rsp\n" ^
                                        (generate consts fvars body (size_of_env + 1) ) ^ "\n" ^
                                        "leave\n" ^
                                        "ret\n" ^
                                        "Lcont_" ^ label_num ^ ":\n"
  | Applic' (x, y) -> let string_func mem acc = acc ^ (generate consts fvars mem size_of_env) ^ "push rax\n" in
                      let pushed_args = (List.fold_right string_func y "") ^ "push " ^ (string_of_int (List.length y)) ^ "\n" in
                      let after_proc = pushed_args ^ (generate consts fvars x size_of_env) in
                      ";;***app*** \n" ^
                      after_proc ^
                      "CLOSURE_ENV r8, rax\n" ^
                      "push r8\n" ^
                      "CLOSURE_CODE r9, rax\n" ^
                      "call r9\n" ^
                      "add rsp, 8*1\n" ^
                      "pop rbx\n" ^
                      "shl rbx, 3\n" ^
                      "add rsp, rbx\n"  
  | ApplicTP'(x, y) ->  let string_func mem acc = acc ^ (generate consts fvars mem size_of_env ) ^ "push rax\n" in
                        let pushed_args = (List.fold_right string_func y "") ^ "push " ^ (string_of_int (List.length y)) ^ "\n" in
                        let after_proc = pushed_args ^ (generate consts fvars x size_of_env ) in
                        after_proc ^
                        "CLOSURE_ENV r8, rax\n" ^
                        "push r8 \n" ^
                        "push qword [rbp + (8 * 1)] \n" ^
                        "push qword [rbp] \n\n" ^

                        "mov r10, qword [rbp + (8 * 3)] \n\n" ^

                        "SHIFT_FRAME "^ (string_of_int ((List.length y) + 4)) ^ "\n" ^
                        "pop rbp \n\n" ^
                        
                        "shl r10, 3 \n" ^
                         "add r10, (8*4) \n" ^
                        "add rsp, r10 \n\n" ^

                        "CLOSURE_CODE r9, rax\n" ^
                        "jmp r9 \n"               
 | LambdaOpt' (x, y, z) when (size_of_env = 0) -> let args_num = ((List.length x) + 1) in
                                                  "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode_" ^ label_num ^ ")\n" ^
                                                  "jmp Lcont_" ^ label_num ^ "\n" ^                                                            
                                                  "Lcode_" ^ label_num ^ ":\n" ^
                                                  "push rbp\n" ^
                                                  "mov rbp , rsp\n" ^
                                                  "mov rbx, qword [rbp + 8 * 3] \n\n; rbx holds num of original args \n " ^ 
                                                  "cmp rbx, " ^ (string_of_int args_num) ^ "\n" ^
                                                  "jb EmptyList_" ^ label_num ^ "\n" ^
                                                  "jmp NotEmptyList_" ^ label_num ^ "\n\n" ^
                                                      
                                                  "EmptyList_" ^ label_num ^ ":\n" ^
                                                  "mov rcx, const_tbl + 1 \n" ^
                                                  "mov rsi, 0\n\n" ^
                                                      
                                                  "LowerStackMem_" ^ label_num ^ ":\n" ^
                                                  "mov rdx, qword [rbp + rsi]\n" ^
                                                  "mov qword [rbp + rsi - 8], rdx\n" ^
                                                  "cmp rsi, " ^ (string_of_int ((3 + args_num - 1) * 8)) ^ "\n" ^
                                                  "je DoneLowering_" ^ label_num ^ "\n" ^   
                                                  "add rsi, 8\n" ^
                                                  "jmp LowerStackMem_" ^ label_num ^ "\n\n" ^
                                                      
                                                  "DoneLowering_" ^ label_num ^ ":\n" ^
                                                  "sub rbp, 8\n" ^

                                                  "mov r12, 0 \n" ^
                                                  "cmp r12, " ^ (string_of_int (List.length x)) ^ " \n" ^
                                                  "jne DontAdd_" ^ label_num ^ "\n" ^
                                                  "add rsi, 8 \n" ^
                                                  "DontAdd_" ^ label_num ^ ":\n" ^

                                                  "mov qword [rbp + rsi + 8], rcx\n ; ADDED +8 \n " ^
                                                  "mov qword [rbp + 3 * 8], " ^ (string_of_int args_num) ^ "\n" ^
                                                  "sub rsp, 8 \n" ^
                                                  "jmp DoneWithTheStack_" ^ label_num ^ "\n\n" ^
                                                      
                                                  "NotEmptyList_" ^ label_num ^ ":\n" ^
                                                  "mov r8, qword [rbp + 3 * 8] \n" ^
                                                  "sub r8, " ^ (string_of_int args_num) ^ "\n" ^
                                                  "add r8, 1 \n\n ; r8 holds the list length \n\n" ^

                                                  "CreateList_" ^ label_num ^ ":\n" ^
                                                  "mov rcx, const_tbl +1 \n" ^
                                                  "mov r9, qword [rbp + 3 * 8] \n" ^
                                                  "add r9, 3 \n" ^
                                                  "shl r9, 3 \n\n ; r9 is the place where the list enters\n\n" ^

                                                  "AddListMem_" ^ label_num ^ ":\n" ^
                                                  "cmp r8, 0 \n" ^
                                                  "je DoneWithList_" ^ label_num ^ "\n" ^
                                                  "mov r10, qword [rbp + r9] \n" ^
                                                  "mov r15, rcx \n" ^
                                                  "mov rcx, 0 \n" ^
                                                  "MAKE_PAIR (rcx, r10, r15) \n" ^
                                                  "sub r9, 8 \n" ^
                                                  "sub r8, 1 \n" ^
                                                  "jmp AddListMem_" ^ label_num ^ "\n\n" ^

                                                  "DoneWithList_" ^ label_num ^ ":\n" ^
                                                  "mov r11, qword [rbp + (3 * 8)] \n" ^
                                                  "add r11, 3 \n" ^
                                                  "shl r11, 3 \n" ^
                                                  "mov qword [rbp + r11], rcx \n" ^
                                                  "mov r12, qword [rbp + (3 * 8)] \n" ^
                                                  "sub r12, " ^ (string_of_int args_num) ^ "\n" ^
                                                  "shl r12, 3 \n\n" ^

                                                  "MovingStackMem_" ^ label_num ^ ":\n" ^
                                                  "sub r11, 8 \n" ^
                                                  "mov r14, r11 \n" ^
                                                  "sub r14, r12 \n" ^
                                                  "mov r13, qword [rbp + r14] \n" ^
                                                  "mov qword [rbp + r11], r13 \n" ^
                                                  "cmp r11, r12 \n" ^
                                                  "je DoneFixingArgs_" ^ label_num ^ "\n" ^   
                                                  "jmp MovingStackMem_" ^ label_num ^ "\n\n" ^

                                                  "DoneFixingArgs_" ^ label_num ^ ":\n" ^
                                                  "add rbp, r12 \n" ^
                                                  "mov qword [rbp + (3 * 8)], " ^ (string_of_int args_num) ^ "\n" ^
                                                  "add rsp, r12 \n" ^
                                                  
                                                  "DoneWithTheStack_" ^ label_num ^ ":\n" ^
                                                  (generate consts fvars z (size_of_env + 1)) ^
                                                  "leave\n" ^
                                                  "ret\n" ^
                                                  "Lcont_" ^ label_num ^ ":\n"  
  | LambdaOpt' (x, y, z) -> let args_num = ((List.length x) + 1) in
                            "\nMALLOC rbx, " ^ (string_of_int (size_of_env * 8) ) ^ "\n" ^
                            "mov r8, " ^ (string_of_int size_of_env) ^ "\n" ^
                            "cmp r8, 1\n" ^
                            "JE AllocateExtEnv0_" ^ label_num^ "\n" ^           
                            "mov rcx, 0\n" ^
                            "mov rdx, qword [rbp + 8 * 2]\n\n" ^

                            "EnvLoop_" ^ label_num^ ":\n" ^
                            "mov rsi, qword [rdx + 8 * rcx]\n" ^
                            "inc rcx\n" ^
                            "mov qword [rbx + 8 * rcx], rsi\n" ^
                            "cmp rcx, " ^ (string_of_int (size_of_env - 1)) ^ "\n" ^
                            "JE AllocateExtEnv0_" ^ label_num^ "\n" ^
                            "jmp EnvLoop_" ^ label_num^ "\n\n" ^
                                
                            "AllocateExtEnv0_" ^ label_num^ ":\n" ^
                            "mov rcx, qword [rbp + 8 * 3]\n" ^
                            "shl rcx, 3\n" ^
                            "MALLOC rdx, rcx\n" ^
                            "mov qword [rbx], rdx\n\n" ^

                            "AllocateExtEnv0PerParam_" ^ label_num^ ":\n" ^
                            "cmp rcx, 0\n" ^
                            "JE MakeClosure_" ^ label_num^ "\n" ^
                            "sub rcx, 8\n" ^
                            "mov rsi, qword [rbp + (8 * 4) + rcx]\n" ^
                            "mov qword [rdx + rcx], rsi\n" ^
                            "jmp AllocateExtEnv0PerParam_" ^ label_num^ "\n\n" ^

                            "MakeClosure_" ^ label_num^ ":\n" ^
                            
                            "MAKE_CLOSURE(rax, rbx, Lcode_" ^ label_num^ ")\n" ^
                            "jmp Lcont_" ^ label_num ^ "\n" ^                                                            
                            "Lcode_" ^ label_num ^ ":\n" ^
                            "push rbp\n" ^
                            "mov rbp , rsp\n" ^
                            "mov rbx, qword [rbp + 8 * 3]\n" ^
                            "cmp rbx, " ^ (string_of_int args_num) ^ "\n" ^
                            "jb EmptyList_" ^ label_num ^ "\n" ^
                            "jmp NotEmptyList_" ^ label_num ^ "\n\n" ^
                                
                            "EmptyList_" ^ label_num ^ ":\n" ^
                            "mov rcx, const_tbl +1 \n" ^
                            "mov rsi, 0\n\n" ^
                                
                            "LowerStackMem_" ^ label_num ^ ":\n" ^
                            "mov rdx, qword [rbp + rsi]\n" ^
                            "mov qword [rbp + rsi - 8], rdx\n" ^
                            "cmp rsi, " ^ (string_of_int ((3 + args_num - 1) * 8)) ^ "\n" ^
                            "je DoneLowering_" ^ label_num ^ "\n" ^   
                            "add rsi, 8\n" ^
                            "jmp LowerStackMem_" ^ label_num ^ "\n\n" ^
                                
                            "DoneLowering_" ^ label_num ^ ":\n" ^
                            "sub rbp, 8\n   ; do we need it??" ^ 

                            "mov r12, 0 \n" ^
                            "cmp r12, " ^ (string_of_int (List.length x)) ^ " \n" ^
                            "jne DontAdd_" ^ label_num ^ "\n" ^
                            "add rsi, 8 \n" ^
                            "DontAdd_" ^ label_num ^ ":\n" ^

                            "mov qword [rbp + rsi + 8], rcx\n ; ADDED +8 \n " ^
                            "mov qword [rbp + 3 * 8], " ^ (string_of_int args_num) ^ "\n" ^
                            "sub rsp, 8 \n" ^
                            "jmp DoneWithTheStack_" ^ label_num ^ "\n\n" ^
                                
                            "NotEmptyList_" ^ label_num ^ ":\n" ^
                            "mov r8, qword [rbp + 3 * 8] \n" ^
                            "sub r8, " ^ (string_of_int args_num) ^ "\n" ^
                            "add r8, 1 \n\n" ^

                            "CreateList_" ^ label_num ^ ":\n" ^
                            "mov rcx, const_tbl +1 \n" ^
                            "mov r9, qword [rbp + 3 * 8] \n" ^
                            "add r9, 3 \n" ^
                            "shl r9, 3 \n\n" ^

                            "AddListMem_" ^ label_num ^ ":\n" ^
                            "cmp r8, 0 \n" ^
                            "je DoneWithList_" ^ label_num ^ "\n" ^
                            "mov r10, qword [rbp + r9] \n" ^
                            "mov r15, rcx \n" ^
                            "mov rcx, 0 \n" ^
                            "MAKE_PAIR (rcx, r10, r15) \n" ^
                            "sub r9, 8 \n" ^
                            "sub r8, 1 \n" ^
                            "jmp AddListMem_" ^ label_num ^ "\n\n" ^

                            "DoneWithList_" ^ label_num ^ ":\n" ^
                            "mov r11, qword [rbp + (3 * 8)] \n" ^
                            "add r11, 3 \n" ^
                            "shl r11, 3 \n" ^
                            "mov qword [rbp + r11], rcx \n" ^
                            "mov r12, qword [rbp + (3 * 8)] \n" ^
                            "sub r12, " ^ (string_of_int args_num) ^ "\n" ^
                            "shl r12, 3 \n\n" ^

                            "MovingStackMem_" ^ label_num ^ ":\n" ^
                            "sub r11, 8 \n" ^
                            "mov r14, r11 \n" ^
                            "sub r14, r12 \n" ^
                            "mov r13, qword [rbp + r14] \n" ^
                            "mov qword [rbp + r11], r13 \n" ^
                            "cmp r11, r12 \n" ^
                            "je DoneFixingArgs_" ^ label_num ^ "\n" ^   
                            "jmp MovingStackMem_" ^ label_num ^ "\n\n" ^

                            "DoneFixingArgs_" ^ label_num ^ ":\n" ^
                            "add rbp, r12 \n" ^
                            "mov qword [rbp + (3 * 8)], " ^ (string_of_int args_num) ^ "\n" ^
                            
                            "add rsp, r12 \n" ^
                            "DoneWithTheStack_" ^ label_num ^ ":\n" ^
                            (generate consts fvars z (size_of_env + 1)) ^
                            "leave \n" ^
                            "ret \n" ^
                            "Lcont_" ^ label_num ^ ":\n"   
  | _ -> "";;

                                                                                                  
end;;

