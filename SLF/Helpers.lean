import Lean

namespace SLF.PP

open Lean Elab Command Term PrettyPrinter
scoped elab "slf_pp" stx:term:51: term => do
  let expr ← elabTerm stx none
  let pretty ← PrettyPrinter.ppExpr expr
  let str := toString pretty
  pure <| toExpr str

scoped elab "#check_expr" t:term: command => do
  let e ← Command.liftTermElabM <| Term.elabTerm t none
  let pp ← Command.liftTermElabM do
    let e ← Term.elabTerm t none
    ppExpr e
  logInfo m!"#check_expr: Expr: `{e}`; Pretty: {pp}"

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

section PrintHypotheses

open Lean Elab Tactic Meta

def printHypothesis: TacticM Unit := do
  let ctx ← MonadLCtx.getLCtx -- get the local context.
  for decl in ctx do
    let declExpr := decl.toExpr
    let declType := decl.type
    let declName := decl.userName

    let displayDeclExpr : Expr → Name := fun expr =>
      match expr.fvarId!.name with
      | .num parent _ => parent
      | name => name

    Lean.logInfo <|
      f!"local decl:\n" ++
      f!"  name: {declName}\n" ++
      f!"  expr: {displayDeclExpr declExpr}\n" ++
      f!"  type: {← ppExpr declType}"

elab "print_hypotheses" : tactic => withMainContext printHypothesis


end PrintHypotheses

section Misc
open Lean

def Lean.Expr.removeMData (e: Expr): Expr :=
  match e with
  | .mdata _ b => b.removeMData
  | _ => e

inductive TacticMark where
  | mark
deriving Repr, Nonempty, Inhabited

macro "tactic_mark" : tactic => `(tactic| have _: TacticMark := TacticMark.mark)

declare_syntax_cat bool (behavior := symbol)
syntax "true" : bool
syntax "false" : bool
syntax "[bool|" bool "]": term
macro_rules
  | `([bool| true]) => `(true)
  | `([bool| false]) => `(false)

def interpBool (stx: TSyntax `bool): Bool :=
  match stx with
  | `(bool| true) => true
  | `(bool| false) => false
  | _ => false

end Misc
