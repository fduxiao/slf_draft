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

section CheckPP
open Lean Elab Tactic Meta

elab "check_goal" exp:term : tactic => withMainContext do
  let goal ← getMainGoal
  let goal ← goal.getType
  let goal ← instantiateMVars goal

  let expected: Expr ← elabTerm exp none
  let eq ← isDefEq goal expected

  if eq then
    pure ()
  else
    throwError m!"expected: `({expected}), got: `({goal})"

example : True := by
  check_goal True
  fail_if_success check_goal False
  trivial

def Helpers.check_decl
  (i: TSyntax `ident)
  (ty: TSyntax `term)
  (tm: TSyntax `term): TacticM Unit
:= do
  let decl ← getLocalDeclFromUserName i.getId
  let declType ← instantiateMVars decl.type
  let expected: Expr ← elabTerm ty none
  if !(← isDefEq declType expected) then
    throwError m!"expected: `({expected}), got: `({declType})"
  let expectedVal ← elabTerm tm none
  let declVal := decl.value?
  if declVal.isNone then
    return ()
  let declVal ← instantiateMVars declVal.get!
  if !(← isDefEq declVal expectedVal) then
    throwError m!"expected value: `({expectedVal}), got: `({declVal})"

elab "check_decl" i:ident ":" ty:term ":=" tm:term : tactic => withMainContext do
  Helpers.check_decl i ty tm

macro "check_decl" i:ident ":" ty:term : tactic => `(tactic| check_decl $i : $ty := _)
macro "check_decl" i:ident ":=" tm:term : tactic => `(tactic| check_decl $i : _ := $tm)

example {P1 P2: Prop}:
  P1 → P2 → P1
:= by
  check_decl P1 : Prop
  fail_if_success check_decl P2 : Nat
  intro H1 H2
  check_decl H1 : P1
  check_decl H2 : P2
  let n : Nat := 3
  check_decl n : Nat := 3
  fail_if_success check_decl n : Nat := 2
  trivial

end CheckPP

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

section DelabNoPP
open Lean

def delabNoPP (e: Expr): MetaM Term := do
  withOptions (fun opts => opts.setBool `pp.all true) do
    PrettyPrinter.delab e
end DelabNoPP

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
