open Utils

module S = Set.Make(struct 
                      type t = expr
                      let compare a b = compare a b
                    end)

type single_type = ENot | IIMpl | IlOr | IrOr | ElAnd | ErAnd
type double_type = EImpl | IAnd
type triple_type = EOr

let string_of_single_type = function ENot -> "[E!!]" | IIMpl -> "[I->]" | IlOr  -> "[Il|]" | IrOr  -> "[Ir|]" | ElAnd -> "[El&]" | ErAnd -> "[Er&]"
let string_of_double_type = function IAnd -> "[I&]"  | EImpl -> "[E->]"
let string_of_triple_type = function EOr -> "[E|]"

type proof_tree =
  | Ax of expr * expr list
  | SingleProof of single_type * expr * (expr list) * proof_tree
  | DoubleProof of double_type * expr * (expr list) * proof_tree * proof_tree
  | TripleProof of triple_type * expr * (expr list) * proof_tree * proof_tree * proof_tree

let ctx_string es = 
  String.concat "," (List.map string_of_expr es)

let tail_str depth ctx e tStr =
  Printf.sprintf "[%d] %s|-%s %s\n" depth (ctx_string ctx) (string_of_expr e) tStr

let rec proof_str depth = function
  | Ax          (   expr, ctx)             ->                                                                                  tail_str depth ctx expr "[Ax]" 
  | SingleProof (t, expr, ctx, p1)         -> proof_str (depth + 1) p1                                                       ^ tail_str depth ctx expr (string_of_single_type t)
  | DoubleProof (t, expr, ctx, p1, p2)     -> proof_str (depth + 1) p1 ^ proof_str (depth + 1) p2                            ^ tail_str depth ctx expr (string_of_double_type t)
  | TripleProof (t, expr, ctx, p1, p2, p3) -> proof_str (depth + 1) p1 ^ proof_str (depth + 1) p2 ^ proof_str (depth + 1) p3 ^ tail_str depth ctx expr (string_of_triple_type t)

let rec append_ctx e = function
  | Ax          (   expr, ctx)             -> Ax          (   expr, e :: ctx)
  | SingleProof (t, expr, ctx, p1)         -> SingleProof (t, expr, e :: ctx, append_ctx e p1)
  | DoubleProof (t, expr, ctx, p1, p2)     -> DoubleProof (t, expr, e :: ctx, append_ctx e p1, append_ctx e p2)
  | TripleProof (t, expr, ctx, p1, p2, p3) -> TripleProof (t, expr, e :: ctx, append_ctx e p1, append_ctx e p2, append_ctx e p3)

let rec var_set = function
  | FalseExpr      -> S.empty
  | Not e          -> var_set e
  | Variable s     -> S.singleton (Variable s)
  | Call (_, a, b) -> S.union (var_set a) (var_set b)

let to_list = S.elements
let string_of_proof_tree pt = proof_str 0 pt
