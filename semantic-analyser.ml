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
  | _ -> false;;

let rec print_list = function 
[] -> ()
| e::l -> print_string e ; print_string " " ; print_list l;;
                       
exception X_syntax_error;;

(* our work *)

let rec find_index_in_list name lst j = 
  match lst with
  | [] -> -1 
  | car::cdr -> (if car = name
                   then j
                   else (find_index_in_list name cdr (j+1)))

let rec find_lex_address var_name env j =
  match env with
  | [] -> (-1, -1)
  | car :: cdr -> (if (List.mem var_name car)
                   then (j, (find_index_in_list var_name car 0))
                   else (find_lex_address var_name cdr (j+1)))



let rec lexical_addresses env params expr =
  match expr with
  | Const(sexp) -> Const'(sexp)
  | Var(var_name) -> (if (List.mem var_name params)
                      then Var'(VarParam(var_name, find_index_in_list var_name params 0))
                      else
                        (let opt_address = find_lex_address var_name env 0 in
                        match opt_address with
                        | (-1, -1) -> (Var'(VarFree(var_name)))
                        | (outer_index, inner_index) -> Var'(VarBound(var_name, outer_index, inner_index))))
  | If(test, dit, dif) -> If'((lexical_addresses env params test), (lexical_addresses env params dit), (lexical_addresses env params dif))
  | Seq(exprs) -> Seq'(List.map (lexical_addresses env params) exprs)
  | Set(set_var, set_value) -> Set'((lexical_addresses env params set_var), (lexical_addresses env params set_value))
  | Def(def_name, def_val) -> Def'((lexical_addresses env params def_name), (lexical_addresses env params def_val))
  | Or(exprs) -> Or'(List.map (lexical_addresses env params) exprs)
  | LambdaSimple(new_params, body) -> (if params = []
                                       then LambdaSimple'(new_params, (lexical_addresses env new_params body))
                                       else LambdaSimple'(new_params, (lexical_addresses (List.append [params] env) new_params body)))
  | LambdaOpt(new_params, opt_param, body) -> (let new_all_params = List.append new_params [opt_param] in
                                               if params = []
                                               then LambdaOpt'(new_params, opt_param, (lexical_addresses env new_all_params body))
                                               else LambdaOpt'(new_params, opt_param, (lexical_addresses (List.append [params] env) new_all_params body)))
  | Applic(operator, args) -> Applic'((lexical_addresses env params operator), (List.map (lexical_addresses env params) args))


let rec tail_calls in_tp expr = 
  match expr with
  | Const'(exp) -> Const'(exp)
  | Var'(var) -> Var'(var)
  | Box'(var) -> Box'(var)
  | BoxGet'(var) -> BoxGet'(var)
  | BoxSet'(var, expr) -> BoxSet'(var, (tail_calls in_tp expr))
  | If'(test, dit, dif) -> If'((tail_calls false test), (tail_calls in_tp dit), (tail_calls in_tp  dif))
  | Seq'(exprs) -> (let rev_list = List.rev exprs in
                    let last = List.hd rev_list in
                    let rest = List.rev (List.tl rev_list) in
                    Seq'(List.append (List.map (tail_calls false) rest) [tail_calls true last]))
  | Set'(set_var, set_value) -> Set'((tail_calls false set_var), (tail_calls false set_value))
  | Def'(def_name, def_value) -> Def'((tail_calls false def_name), (tail_calls false def_value))
  | Or'(exprs) -> (let rev_list = List.rev exprs in
                   let last = List.hd rev_list in
                   let rest = List.rev (List.tl rev_list) in
                   Or'(List.append (List.map (tail_calls false) rest) [tail_calls true last]))
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (tail_calls true body))
  | LambdaOpt'(params, opt_param, body) -> LambdaOpt'(params, opt_param, (tail_calls true body))
  | Applic'(operator, args) -> (if in_tp
                                then ApplicTP'((tail_calls false operator), (List.map (tail_calls false) args))
                                else Applic'((tail_calls false operator), (List.map (tail_calls false) args)))
  | ApplicTP'(operator, args) -> ApplicTP'((tail_calls false operator), (List.map (tail_calls false) args))



let check = fun a b -> a || b

let is_boxing read_list write_list = 
  let check_writes num = 
    let remaining = List.filter (fun number -> number != num) write_list in
    ((List.length remaining) > 0) in
  let lst = List.map (check_writes) read_list in
  List.fold_right check lst false;;


let rec boxing expr =   
  match expr with
  | Const'(exp) -> Const'(exp)
  | Var'(var) -> Var'(var)
  | Box'(var) -> Box'(var)
  | BoxGet'(var) -> BoxGet'(var)
  | BoxSet'(var, exp) -> BoxSet'(var, (boxing exp))
  | If'(test, dit, dif) -> If'((boxing test), (boxing dit), (boxing dif))
  | Seq'(exps) -> Seq'(List.map boxing exps)
  | Set'(set_var, set_val) -> Set'((boxing set_var), (boxing set_val))
  | Def'(def_var, def_val) -> Def'((boxing def_var), (boxing def_val))
  | Or'(exps) -> Or'(List.map boxing exps)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (boxing (handle_lambda params body)))
  | LambdaOpt'(params, opt_param, body) -> LambdaOpt'(params, opt_param, (boxing (handle_lambda (List.append params [opt_param]) body)))
  | Applic'(operator, args) -> Applic'((boxing operator), (List.map boxing args))
  | ApplicTP'(operator, args) -> ApplicTP'((boxing operator), (List.map boxing args));



(*and handle_lambda params body =
 match exprs with
  | Seq'(exps) -> (let dont_care = (for i = 0 to ((List.length params) - 1) do
                        (check_box_var (List.nth params i) exps)
                        done) in
                    Seq'(exps))
  | _ -> boxing exprs;*)

and handle_lambda params body = 
  match params with
  | param :: rest -> handle_lambda rest (check_box_var param body)
  | [] -> body;




and check_box_var param body =
  let global_reads = ref [] in
  let global_writes = ref [] in
  let add_to_reads branch_num = 
    (if (not (List.mem branch_num !global_reads))
    then global_reads := List.append !global_reads [branch_num]) in
  let add_to_writes branch_num = 
    (if (not (List.mem branch_num !global_writes))
    then global_writes := List.append !global_writes [branch_num]) in
  
  let rec check_branch param branch_num expr' =
    (match expr' with
    | Const'(exp) -> Const'(exp)
    | Var'(var) -> (match var with
                    | VarBound(name, major, minor) when name = param -> (let dont_care = add_to_reads branch_num in
                                                                        Var'(var))
                    | _ -> Var'(var))
    | Box'(var) -> Box'(var)
    | BoxGet'(var) -> BoxGet'(var)
    | BoxSet'(var, exp) -> BoxSet'(var, (check_branch param branch_num exp))
    | If'(test, dit, dif) -> If'((check_branch param branch_num test), (check_branch param branch_num dit), (check_branch param branch_num dif))
    | Seq'(exps) -> Seq'(List.map (check_branch param branch_num) exps)
    | Set'(set_var, set_val) -> (match set_var with
                                | Var'(VarBound(name, major, minor)) when name = param -> (let dont_care = add_to_writes branch_num in
                                                                                           Set'(set_var, (check_branch param branch_num set_val)))
                                | _ -> Set'((check_branch param branch_num set_var), (check_branch param branch_num set_val)))
    | Def'(def_var, def_val) -> Def'((check_branch param branch_num def_var), (check_branch param branch_num def_val))
    | Or'(exps) -> Or'(List.map (check_branch param branch_num) exps)
    | LambdaSimple'(params, body) -> (if (List.mem param params)
                                      then LambdaSimple'(params, body)
                                      else LambdaSimple'(params, (check_branch param branch_num body)))
    | LambdaOpt'(params, opt_param, body) -> (if (List.mem param (List.append params [opt_param]))
                                              then LambdaOpt'(params, opt_param, body)
                                              else LambdaOpt'(params, opt_param, (check_branch param branch_num body)))
    | Applic'(operator, args) -> Applic'((check_branch param branch_num operator), (List.map (check_branch param branch_num) args))
    | ApplicTP'(operator, args) -> ApplicTP'((check_branch param branch_num operator), (List.map (check_branch param branch_num) args))) in

  let help_func expr =
    (let next_num = Random.int 9999999 in
    check_branch param next_num expr) in
  let rec main_func body = 
    (match body with
    | Const'(exp) -> Const'(exp)
    | Var'(var) -> Var'(var)
    | Box'(var) -> Box'(var)
    | BoxGet'(var) -> BoxGet'(var)
    | BoxSet'(var, exp) -> BoxSet'(var, (help_func exp))
    | If'(test, dit, dif) -> If'((help_func test), (help_func dit), (help_func dif))
    | Seq'(exps) -> Seq'(List.map help_func exps)
    | Set'(set_var, set_val) -> Set'((help_func set_var), (help_func set_val))
    | Def'(def_var, def_val) -> Def'((help_func def_var), (help_func def_val))
    | Or'(exps) -> Or'(List.map help_func exps)
    | LambdaSimple'(params, body) -> boxing (LambdaSimple'(params, body))
    | LambdaOpt'(params, opt_param, body) -> boxing (LambdaOpt'(params, opt_param, body))
    | Applic'(operator, args) -> Applic'((help_func operator), (List.map help_func args))
    | ApplicTP'(operator, args) -> ApplicTP'((help_func operator), (List.map help_func args))) in
  
  let ret = main_func body in
  let r = Printf.printf "\n\n\n\nreads %d\n" (List.length !global_reads) in
  let r = Printf.printf "writes %d\n\n\n\n\n\n" (List.length !global_writes) in
  if (is_boxing !global_reads !global_writes)
  then Const'(Void)
  else ret;;
  (*let r = Printf.printf "reads %d\n" (List.length !global_reads) in
  let r = Printf.printf "writes %d\n\n\n\n\n\n" (List.length !global_writes) in
  ret;;*) 




let lex e = tail_calls false (lexical_addresses [] [] (tag_parser e))

let lex2 e = lexical_addresses [] [] (tag_parser e)

let lex3 e = boxing (lex e)

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let annotate_lexical_addresses e = raise X_not_yet_implemented;;

let annotate_tail_calls e = raise X_not_yet_implemented;;

let box_set e = raise X_not_yet_implemented;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)



(*let rec rename_params expr =
  match expr with
  | LambdaSimple'(params, body) -> LambdaSimple'()

let rec rename_vars env params expr = 
  match expr with
  | Var'(var) -> (match var with
                | VarParam(name, index) -> (if (List.mem name params)
                                            then VarParam())
                | VarBound(name, major, minor) -> VarBound((change_name name), major, minor)
                | _ -> _ )
  | If'(test, dit, dif) -> If'((rename_vars env params test), (rename_vars env params dit), (rename_vars env params))*)

(*let rec boxing expr = 
  match expr with
  | Const'(exp) -> Const'(exp)
  | Var'(var) -> Var'(var)
  | Box'(var) -> Box'(var)
  | BoxGet'(var) -> BoxGet'(var)
  | BoxSet'(var, exp) -> BoxSet'(var, (boxing exp))
  | If'(test, dit, dif) -> If'((boxing test), (boxing dit), (boxing dif))
  | Seq'(exprs) -> Seq'(List.map boxing exprs)
  | Set'(set_var, set_val) -> Set'((boxing set_var), (boxing set_val))
  | Def'(def_name, def_value) -> Def'((boxing def_name), (boxing def_value))
  | Or'(exprs) -> Or'(List.map boxing exprs)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (handle_lambda params body));


and handle_lambda params expr =*)


  (*let rec is_read param expr = 
    match expr with
    | Const'(exp) -> false
    | Var'(var) -> (match var with
                    | VarParam(name, index) when name = param -> true
                    | VarBound(name, major, minor) when name = param -> true
                    | VarFree(name) when name = param -> false
                    |_ -> false)
    | Box'(var) -> false
    | BoxGet'(var) -> false
    | BoxSet'(var, exp) -> false
    | If'(test, dit, dif) -> (let test_res = is_read param test in
                              let dit_res = is_read param dit in
                              let dif_res = is_read param dif in
                              (test_res || dit_res || dif_res))
    | Seq'(exprs) -> (let bools = List.map (fun exp -> is_read param exp) exprs in
                      List.fold_right check bools false)
    | Set'(set_var, set_val) -> (match set_var with
                                 | Var'(VarParam(name, index)) -> (is_read param set_val)
                                 | Var'(VarBound(name, major, minor)) -> (is_read param set_val)
                                 | _ ->  check (is_read param set_var) (is_read param set_val))
    | Def'(def_var, def_val) -> check (is_read param def_var) (is_read param def_val)
    | Or'(exprs) -> (let bools = List.map (fun exp -> is_read param exp) exprs in
                      List.fold_right check bools false)
    | LambdaSimple'(params, body) -> (if (List.mem param params)
                                      then false
                                      else (is_read param body))
    | LambdaOpt'(params, opt_param, body) -> (if (List.mem param (List.append params [opt_param]))
                                      then false
                                      else (is_read param body))
    | Applic'(operator, args) -> (let operator_res = is_read param operator in
                                 let args_res = List.fold_right check (List.map (fun exp -> is_read param exp) args) false in
                                 check operator_res args_res)
    | ApplicTP'(operator, args) -> (let operator_res = is_read param operator in
                                 let args_res = List.fold_right check (List.map (fun exp -> is_read param exp) args) false in
                                 check operator_res args_res) *)