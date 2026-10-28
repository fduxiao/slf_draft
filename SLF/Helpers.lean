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

section TacticMark

open Lean Elab Tactic Meta Term

inductive TacticMark where
  | mark
deriving Repr, Nonempty, Inhabited

macro "tactic_mark" : tactic => `(tactic| have tactic_mark: TacticMark := TacticMark.mark)

def declAfterMark: MetaM (Array (LocalDecl)) := do
  let mut started := false
  let mut result: Array LocalDecl := #[]
  let ctx ← MonadLCtx.getLCtx -- get the local context.
  for decl in ctx do
    let declType := decl.type
    -- check if the current declaration is a TacticMark
    if ← isDefEq declType (mkConst ``TacticMark) then
      started := true
      continue
    if not started then
      continue
    result := result.push decl
  return result

elab "revert_after_mark" : tactic => withMainContext do
  let decls ← declAfterMark
  liftMetaTactic <| fun mvarId => do
    let ⟨_, mvarId⟩ ← mvarId.revert ( (fun decl => decl.fvarId) <$> decls)
    return [mvarId]

def Helpers.clear! (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId := do
    mvarId.checkNotAssigned `clear_mark
    let lctx ← getLCtx
    unless lctx.contains fvarId do
      throwTacticEx `clear_mark mvarId m!"unknown variable '{mkFVar fvarId}'"
    let tag ← mvarId.getTag
    let mvarDecl ← mvarId.getDecl
    let lctx := lctx.erase fvarId
    let localInsts ← getLocalInstances
    let localInsts := match localInsts.findFinIdx? fun localInst => localInst.fvar.fvarId! == fvarId with
      | none => localInsts
      | some idx => localInsts.eraseIdx idx
    let newMVar ← mkFreshExprMVarAt lctx localInsts mvarDecl.type MetavarKind.syntheticOpaque tag
    mvarId.assign newMVar
    pure newMVar.mvarId!

elab "clear_mark!" : tactic => withMainContext do
  let goal ← getMainGoal
  let ctx ← MonadLCtx.getLCtx -- get the local context.
  for decl in ctx do
    let declType := decl.type
    -- check if the current declaration is a TacticMark
    if ! (← isDefEq declType (mkConst ``TacticMark)) then
      continue
    let goal ← Helpers.clear! goal decl.fvarId
    replaceMainGoal [goal]

elab "clear_mark" : tactic => withMainContext do
  let goal ← getMainGoal
  let ctx ← MonadLCtx.getLCtx -- get the local context.
  let mut success := false
  for decl in ctx do
    let declType := decl.type
    -- check if the current declaration is a TacticMark
    if ! (← isDefEq declType (mkConst ``TacticMark)) then
      continue
    let goal ← goal.clear decl.fvarId
    replaceMainGoal [goal]
    success := true
  if !success then
    throwError "no TacticMark found"

macro "clear_mark'" : tactic => `(tactic| repeat any_goals clear_mark)

example {P Q R: Prop}:
  P → Q → R → True
:= by
  tactic_mark
  intros
  guard_target = True
  revert_after_mark
  guard_target = (P → Q → R → True)
  clear_mark!
  intros
  trivial

-- Why do I need the `clear_mark` tactic? See the following.
example:
  (forall {x: Nat}, 0 ≤ x → False) → False
:= by
  have K: Unit := ()
  intro H
  apply H
  . fail_if_success clear K
    lia
  . exact default

example (n: Nat):
  (forall {x: Nat}, 0 ≤ x → False) → False
:= by
  have h: TacticMark := TacticMark.mark
  intro H
  apply H <;> clear_mark! <;> revert n
  . guard_target = ∀ (n : Nat), 0 ≤ _
    lia
  . exact default

example:
  (forall {x: Nat}, 0 ≤ x → False) → False
:= by
  have h: TacticMark := TacticMark.mark
  intro H
  apply H <;> clear_mark!
  . guard_target = 0 ≤ ?x
    lia
  . exact default

end TacticMark

section Misc
open Lean

def Lean.Meta.isDefEqOpaque (e1 e2: Expr): MetaM Bool := do
  withAssignableSyntheticOpaque do
    isDefEq e1 e2

def Lean.Expr.removeMData (e: Expr): Expr :=
  match e with
  | .mdata _ b => b.removeMData
  | _ => e

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

declare_syntax_cat dir (behavior := symbol)
syntax "←" : dir
syntax "<-" : dir
syntax "→" : dir
syntax "->" : dir
def interpDir (stx: TSyntax `dir): Bool :=
  match stx with
  | `(dir| ←) => false
  | `(dir| <-) => false
  | `(dir| →) => true
  | `(dir| ->) => true
  | _ => true


end Misc
