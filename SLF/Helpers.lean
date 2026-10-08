import Lean

namespace SLF.PP

open Lean Elab Command Term
scoped elab "slf_pp" stx:term:51: term => do
  let expr ← elabTerm stx none
  let pretty ← PrettyPrinter.ppExpr expr
  let str := toString pretty
  pure <| toExpr str

end SLF.PP

section TryCommand
open Lean Elab Command Term

elab "#try " _name:declId ? sig:(declSig) ":=" val:term: command =>
  liftTermElabM
    try
      let ⟨binders, typeStx⟩ := expandDeclSig sig
      elabBinders binders.getArgs fun _xs => do
        let tp ← elabType typeStx
        discard $ elabTermEnsuringType val tp
        synthesizeSyntheticMVarsNoPostponing
    catch | e => throwError e.toMessageData

end TryCommand
