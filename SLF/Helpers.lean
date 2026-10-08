import Lean

namespace SLF.PP

open Lean Elab Command Term
scoped elab "slf_pp" stx:term:51: term => do
  let expr ← elabTerm stx none
  let pretty ← PrettyPrinter.ppExpr expr
  let str := toString pretty
  pure <| toExpr str

end SLF.PP
