type bi_oper = And | Imply | Or

let string_of_bi_oper = function
  | Or    -> "|"
  | And   -> "&"
  | Imply -> "->"

type expr = Variable of string | Not of expr | Call of bi_oper * expr * expr | FalseExpr

let rec string_of_expr = function
  | Variable v      -> v
  | Not e           -> "(!" ^ (string_of_expr e) ^ ")"
  | Call (op, a, b) -> "(" ^ (string_of_expr a) ^ (string_of_bi_oper op) ^ (string_of_expr b) ^ ")"
  | FalseExpr       -> "_|_"

let _I_ = FalseExpr

let (&.&) a b = Call (And, a, b)    (* & -> left-assoc,  ~prior: 7 *)
let (&.|) a b = Call (Or, a, b)     (* & -> left-assoc,  ~prior: 6 *)
let (@->) a b = Call (Imply, a, b)  (* @ -> right-assoc, ~prior: 5 *)
