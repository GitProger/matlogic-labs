open Lexer
open Parser
open Utils
open Base
open Helpers

let strEvaluation = function
 | (Variable v)                      -> v ^ ":=T"
 | (Call (_, Variable v, FalseExpr)) -> v ^ ":=F"
 | _ -> failwith "unable to evaluate"
 
let strRefutable e = Printf.sprintf "Formula is refutable [%s]" (String.concat "," (List.map strEvaluation e))

let main = 
  let expr = Parser.main Lexer.main @@ Lexing.from_string @@ read_line () in
    let (res, ctx, ok) = proof (to_list @@ var_set @@ expr) expr [] in
      if ok then print_string (string_of_proof_tree res)
            else print_endline (strRefutable ctx) ;;
