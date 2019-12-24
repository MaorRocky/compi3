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
  | If'(test, dit, dif) -> If'((tail_calls false test), (tail_calls true dit), (tail_calls true dif))
  | Seq'(exprs) -> (let rev_list = List.rev exprs in
                    let last = List.hd rev_list in
                    let rest = List.rev (List.tl rev_list) in
                    Seq'(List.append (List.map (tail_calls false) rest) [tail_calls true last]))
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (tail_calls true body))
  | LambdaOpt'(params, opt_param, body) -> LambdaOpt'(params, opt_param, (tail_calls true body))
  | Applic'(operator, args) -> (if in_tp
                                then ApplicTP'((tail_calls false operator), (List.map (tail_calls false) args))
                                else Applic'((tail_calls false operator), (List.map (tail_calls false) args)))

let lex e = tail_calls false (lexical_addresses [] [] (tag_parser e))

let lex2 e = lexical_addresses [] [] (tag_parser e)


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
