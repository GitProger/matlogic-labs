open Utils
open Base

let proof_operation op a b ctx (pa, pa_ok) (pb, pb_ok) =
  match op with
  | And when not pb_ok              -> (SingleProof (IIMpl, (a &.& b) @-> _I_, ctx, DoubleProof (EImpl, _I_, (a &.& b)::ctx, append_ctx (a &.& b) pb, SingleProof (ErAnd, b, (a &.& b)::ctx, Ax (a &.& b, (a &.& b)::ctx)))), false)
  | And when not pa_ok              -> (SingleProof (IIMpl, (a &.& b) @-> _I_, ctx, DoubleProof (EImpl, _I_, (a &.& b)::ctx, append_ctx (a &.& b) pa, SingleProof (ElAnd, a, (a &.& b)::ctx, Ax (a &.& b, (a &.& b)::ctx)))), false)
  | And when pa_ok && pb_ok         -> (DoubleProof (IAnd, a &.& b, ctx, pa, pb), true)
  | Or  when pa_ok                  -> (SingleProof (IlOr, a &.| b, ctx, pa    ), true)
  | Or  when pb_ok                  -> (SingleProof (IrOr, a &.| b, ctx, pb    ), true)
  | Or  when not pa_ok && not pb_ok -> (SingleProof (IIMpl, (a &.| b) @-> _I_, ctx, TripleProof (EOr  , _I_, (a &.| b)::ctx,
                                                                                                      DoubleProof (EImpl, _I_, a::(a &.| b)::ctx, append_ctx a (append_ctx (a &.| b) pa), Ax (a, a::(a &.| b)::ctx)),
                                                                                                      DoubleProof (EImpl, _I_, b::(a &.| b)::ctx, append_ctx b (append_ctx (a &.| b) pb), Ax (b, b::(a &.| b)::ctx)),
                                                                                                      Ax (a &.| b, (a &.| b)::ctx))), false)
  | Imply when pb_ok                -> (SingleProof (IIMpl, a @-> b, ctx, append_ctx a pb), true)
  | Imply when not pa_ok            -> (SingleProof (IIMpl, a @-> b, ctx,
                      DoubleProof (EImpl, b, a::ctx,
                        SingleProof (IIMpl, _I_ @-> b, a::ctx, SingleProof (ENot, b, (_I_::a::ctx), Ax (_I_, (b @-> _I_)::_I_::a::ctx))),
                        DoubleProof (EImpl, _I_, a::ctx, append_ctx a pa, Ax (a, a::ctx)))), true)          
  | Imply when pa_ok && not pb_ok   -> (SingleProof (IIMpl, (a @-> b) @-> _I_, ctx,
                      DoubleProof (EImpl, _I_, (a @-> b)::ctx, append_ctx (a @-> b) pb,
                        DoubleProof (EImpl, b, (a @-> b)::ctx, Ax (a @-> b, (a @-> b)::ctx), append_ctx (a @-> b) pa))), false)
  | _ -> failwith "impossible"

let rec proof_ctx ctx expr =
  match expr with
  | FalseExpr       -> (SingleProof (IIMpl, _I_ @-> _I_, ctx, Ax (_I_, _I_ :: ctx)), false)
  | Call (op, a, b) -> proof_operation op a b ctx (proof_ctx ctx a) (proof_ctx ctx b)
  | Variable s      -> if List.mem (Variable s) ctx 
                          then (Ax (Variable s        , ctx),  true)
                          else (Ax (Variable s @-> _I_, ctx), false)
  | _ -> failwith "impossible"

(*   `&` > `|` > `->`    *)
let rev   x    = x @-> _I_
let nn    x    = (rev x) @-> _I_
let both  x    = x &.| (rev x)
let nboth x    = rev (both x)
let f_ax x ctx = Ax (nboth x, ctx)

(* let basicProof x ctx = Ax (x, ctx) *)
let basicProof x ctx = 
  SingleProof (ENot, (both x), ctx, (append_ctx (nboth x)
    (DoubleProof (EImpl, _I_, ctx,
      DoubleProof (EImpl, (nn x), ctx,
        DoubleProof (EImpl, ((nboth x) @-> (rev x) @-> _I_), ctx,
          SingleProof (IIMpl, (((rev x) @-> (both x)) @-> (nboth x) @-> (rev x) @-> _I_), ctx, 
            (append_ctx ((rev x) @-> (both x))
                        (SingleProof (IIMpl, ((nboth x) @-> (rev x) @-> _I_), ctx, 
                          (append_ctx (nboth x)
                            (SingleProof (IIMpl, (nn x), ctx, (append_ctx (rev x)
                              (DoubleProof (EImpl, _I_, ctx, (f_ax x ctx), SingleProof (IrOr, (both x), ctx, Ax ((rev x), ctx)))))))))))),
          SingleProof (IIMpl, ((rev x) @-> (both x)), ctx,
            (append_ctx (rev x) (SingleProof (IrOr, (both x), ctx, (Ax ((rev x), ctx))))))),
        (f_ax x ctx)),
      DoubleProof (EImpl, (rev x), ctx,
        DoubleProof (EImpl, ((nboth x) @-> (rev x)), ctx,
          SingleProof (IIMpl, ((x @-> (both x)) @-> (nboth x) @-> (rev x)), ctx,
            (append_ctx (x @-> (both x)) 
                        (SingleProof (IIMpl, ((nboth x) @-> (rev x)), ctx,
                          (append_ctx (nboth x) 
                            (SingleProof (IIMpl, (rev x), ctx, (append_ctx x
                              (DoubleProof (EImpl, _I_, ctx, (f_ax x ctx), SingleProof (IlOr, (both x), ctx, Ax (x, ctx)))))))))))),
          SingleProof (IIMpl, (x @-> (both x)), ctx, 
            (append_ctx x (SingleProof (IlOr, (both x), ctx, Ax (x, ctx)))))),
        (f_ax x ctx))))))

let rec proof varset expr ctx = 
  match varset with
  | []            -> let (proof_res, ok) = proof_ctx ctx expr in (proof_res, ctx, ok)
  | (x::ctx_tail) -> let (proof_t, ctx_t, ok_t) = proof ctx_tail expr (x::ctx) and
                         (proof_f, ctx_f, ok_f) = proof ctx_tail expr ((rev x)::ctx) in 
                            if not ok_t then (proof_t, ctx_t, ok_t) else
                            if not ok_f then (proof_f, ctx_f, ok_f) else
                            (TripleProof (EOr, expr, ctx, proof_t, proof_f, (basicProof x ctx)), ctx, true)
