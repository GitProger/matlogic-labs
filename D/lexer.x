{ 
module Lexer where 
import Utils
}

%wrapper "basic"

tokens :-
  $white+            ;
  [A-Z][A-Z 0-9\'’]* {\n -> VarTkn n}
  \(                 {const LeftBrTkn}
  \)                 {const RightBrTkn}
  \&                 {const AndTkn}
  "->"               {const ImplyTkn}
  \!                 {const NotTkn}
  \|                 {const OrTkn}
  \,                 {const CommaTkn}
  "|-"               {const TurnstileTkn}
  "_|_"              {const EmptyTkn}
