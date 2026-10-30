import SLF.WP.WPGen

namespace SLF.WPGen

section XWPDisp
open Heap Lang XSimp
/-!
Display
-/

/--
This is just a display notation for XWP triples.
`XWPDisp H F Q = H ==> (mkStruct F) Q`, which is displayed as
```
Pre H
CODE F
POST Q
```
-/
abbrev XWPDisp (H: HProp) (F: Formula) (Q: Val → HProp) := H ==> (mkStruct F) Q

theorem XWPDisp.start {H F Q}:
  H ==> mkStruct F Q ↔
  XWPDisp H F Q
:= by
  unfold XWPDisp
  simp

syntax
  ppGroup("Pre" ppSpace term)
  ppDedent(ppLine "CODE")
  ppGroup(ppLine xwp_code)
  ppDedent(ppLine "POST" ppSpace term)
: term

macro_rules
  | `(Pre $H CODE $F POST $Q) => `(XWPDisp $H <[ $F ]> $Q)

@[app_unexpander XWPDisp]
def unexpandXWPDisp : Lean.PrettyPrinter.Unexpander
  | `($_ $H $F $Q) => do
    let F ← parseToXwp F
    `(Pre $H CODE $F POST $Q)
  | _ => throw ()

macro "xdisplay" : tactic => `(tactic| try rw [XWPDisp.start])

open XLemmas in
example (p: Loc) (n: Int):
  let incr: Val := [slf|
    vfun p =>
       let n := !p in
       let m := n + 1 in
       p := m
  ]
  Triple (.app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n + 1: Int))
:= by
  apply xwp_fun rfl; simp [wpgen, Term.isubst]; xdisplay
  apply xstruct; apply xlet; xdisplay
  apply xstruct; apply xapp (Triple.get); xsimp; xdisplay
  apply xstruct; apply xlet; xdisplay
  apply xstruct; apply xapp (Triple.add); xsimp; xdisplay
  apply xstruct; apply xapp (Triple.set); xsimp

end XWPDisp

section XTactics
open Lean Meta Elab Tactic Heap XSimp XHelpers Qq

open Lang in
def XHelpers.parseTarget?: TacticM (Option (Q(HProp) × Q(Formula) × Q(Val → HProp))) := do
  let goal: Q(Prop) ← getMainGoalQ
  match goal with
  | ~q($H ==> mkStruct $F $Q) =>
    return (H, F, Q)
  | ~q($H ==> (show Formula from $F) $Q) =>
    return (H, F, Q)
  | _ => return none

elab "xtarget?": tactic => withMainContext do
  let goal ← getMainGoalQ
  match goal with
  | ~q($H ==> mkStruct $F $Q) => logInfo m!"Target: \n\tH = {H};\n\tF = {F};\n\tQ = {Q}"
  | _ => logInfo m!"No XWP target found {goal}"

macro "xstruct": tactic => `(tactic| apply XLemmas.xstruct)
elab "xstruct?": tactic => withMainContext do
  let goal: Q(Prop) ← getMainGoalQ
  match goal with
  | ~q($H ==> mkStruct $F $Q) =>
    evalTactic <| ← `(tactic| xstruct)
  | _ => pure ()

macro "xval": tactic => `(tactic| xstruct? <;> apply XLemmas.xval <;> xdisplay)
macro "xlet": tactic => `(tactic| xstruct? <;> apply XLemmas.xlet <;> xdisplay)
macro "xseq": tactic => `(tactic| xstruct? <;> apply XLemmas.xseq <;> xdisplay)

elab "xlet_xseq?": tactic => withMainContext do
  let some (_, F, _) ← XHelpers.parseTarget? | throwError "xlet_xseq? failed: could not parse target"
  match F with
  | ~q(wpgen.let $F1 $F2) =>
    evalTactic <| ← `(tactic| xlet)
  | ~q(wpgen.seq $F1 $F2) =>
    evalTactic <| ← `(tactic| xseq)
  | _ => pure ()

macro "xif!": tactic => `(tactic| xlet_xseq? <;> xstruct? <;> apply XLemmas.xif <;> try simp <;> xdisplay)
macro "xif_true": tactic => `(tactic| xlet_xseq? <;> xstruct? <;> apply XLemmas.xif_true <;> xdisplay)
macro "xif_false": tactic => `(tactic| xlet_xseq? <;> xstruct? <;> apply XLemmas.xif_false <;> xdisplay)

open Lang in
elab "xif": tactic => withMainContext do
  evalTactic <| ← `(tactic| xlet_xseq? <;> xstruct?)
  let goal: Q(Prop) ← getMainGoalQ
  match goal with
  | ~q($H ==> (wpgen.if $F1 $F2 $F3) $Q) =>
    match F1 with
    | ~q([slf| true]) => evalTactic <| ← `(tactic| apply XLemmas.xif_true)
    | ~q([slf| false]) => evalTactic <| ← `(tactic| apply XLemmas.xif_false)
    | _ => evalTactic <| ← `(tactic| apply XLemmas.xif <;> try simp)
  | _ => throwError "xif tactic failed: {goal} is not an if structure"
  evalTactic <| ← `(tactic| xdisplay)

macro "xtriple":tactic => `(tactic| intros <;> apply XLemmas.xtriple)
macro "xtriple?": tactic => `(tactic| try xtriple)

partial def XHelpers.getTermAppFn (t: Q(Lang.Term)) : MetaM Q(Lang.Term) := do
  match t with
  | ~q(Lang.Term.app $f $args) =>
    XHelpers.getTermAppFn f
  | _ => pure t

def XHelpers.parseAppOp! : TacticM Q(Lang.Prim) := do
  let some (_, F, _) ← XHelpers.parseTarget? | throwError "parseOp! failed: could not parse target"
  match F with
  | ~q(wpgen.app $t) =>
    let appFn ← XHelpers.getTermAppFn t
    match appFn with
    | ~q(Lang.Term.val (Lang.Val.prim $op)) =>
      pure op
    | _ => throwError "parseAppOp! failed: function {appFn} is not a Prim"
  | _ => throwError "parseOp! failed: could not parse target {F}"

/--
`xapp_op` tactic applies the `xapp_op` lemma to the current goal, after parsing the target structure.
-/
elab "xapp_op": tactic => withMainContext do
  evalTactic <| ← `(tactic| xlet_xseq? <;> xstruct?)
  let op ← XHelpers.parseAppOp!
  let op := op.constName!
  let thmName ← match op with
    | ``Lang.Prim.ref => pure ``Triple.ref
    | ``Lang.Prim.get => pure ``Triple.get
    | ``Lang.Prim.set => pure ``Triple.set
    | ``Lang.Prim.free => pure ``Triple.free
    | ``Lang.Prim.neg => pure ``Triple.neg
    | ``Lang.Prim.opp => pure ``Triple.opp
    | ``Lang.Prim.eq => pure ``Triple.eq
    | ``Lang.Prim.add => pure ``Triple.add
    | ``Lang.Prim.neq => pure ``Triple.neq
    | ``Lang.Prim.sub => pure ``Triple.sub
    | ``Lang.Prim.mul => pure ``Triple.mul
    | ``Lang.Prim.div => pure ``Triple.div
    | ``Lang.Prim.mod => pure ``Triple.mod
    | ``Lang.Prim.rand => pure ``Triple.rand
    | ``Lang.Prim.le => pure ``Triple.le
    | ``Lang.Prim.lt => pure ``Triple.lt
    | ``Lang.Prim.ge => pure ``Triple.ge
    | ``Lang.Prim.gt => pure ``Triple.gt
    | _ => throwError "xapp_op: unsupported operation"
  let id := mkIdent thmName
  let xapp := mkIdent ``XLemmas.xapp
  evalTactic <| ← `(tactic| apply $xapp $id; any_goals xsimp; xdisplay)

macro "xapp" t:term : tactic => `(tactic|
  (xlet_xseq?; xstruct?; apply XLemmas.xapp; apply $t; (try any_goals xsimp); all_goals xdisplay)
)

syntax "xfun" (" with " term )? : tactic

macro_rules
  | `(tactic| xfun) => `(tactic|
    xstruct?; xlet_xseq?; apply XLemmas.xfun_nospec; (try any_goals xsimp); all_goals xdisplay)
  | `(tactic| xfun with $t) => `(tactic|
    xstruct?; xlet_xseq?; apply XLemmas.xfun_spec (S := $t); (try any_goals xsimp); all_goals xdisplay)

syntax "xfix" ("with" term)? : tactic
macro_rules
  | `(tactic| xfix) => `(tactic|
    xstruct?; xlet_xseq?; apply XLemmas.xfix_nospec; (try any_goals xsimp); all_goals xdisplay)
  | `(tactic| xfix with $t) => `(tactic|
    xstruct?; xlet_xseq?; apply XLemmas.xfix_spec (S := $t); (try any_goals xsimp); all_goals xdisplay)

macro "xwp" : tactic =>
  `(tactic|
    (try simp_all) <;>
    (first | apply XLemmas.xwp_fun (by rfl) | apply XLemmas.xwp_fix (by rfl)) <;>
    (try simp [wpgen, Lang.Term.isubst, wpgen.var, MSubst.Context.lookup, List.lookup]) <;>
    xdisplay)

open Lang
elab "xstep" : tactic => withMainContext do
  evalTactic <| ← `(tactic| xstruct? <;> xlet_xseq?)
  let some (_, F, _) ← XHelpers.parseTarget? | throwError "parseOp! failed: could not parse target"
  match F with
  | ~q(wpgen.val $v) =>
    evalTactic <| ← `(tactic| xval)
  | ~q(wpgen.app $t) =>
    let appFn ← XHelpers.getTermAppFn t
    match appFn with
    | ~q(Lang.Term.val (Lang.Val.prim $op)) =>
      evalTactic <| ← `(tactic| xapp_op)
    | _ => throwError "xstep: unsupported app {appFn}"
  | ~q(wpgen.if $t $F1 $F2) =>
    match t with
    | ~q([slf| true]) => evalTactic <| ← `(tactic| xif_true)
    | ~q([slf| false]) => evalTactic <| ← `(tactic| xif_false)
    | _ => throwError "xstep: unsupported if condition {t}"
  | _ => throwError "xstep: unsupported target {F}"

macro "xsteps" : tactic => `(tactic| repeat xstep)

namespace XWPNotationExamples
open Lang XLemmas

example (p: Loc) (n: Int):
  Triple (.app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n + 1: Int))
:= by
  xwp
  xlet
  xapp_op
  xlet
  xapp_op
  xapp_op

example {n v: Int}:
  let prog: Val := [slf|
    vfun n =>
      let v1 := [n + v] in
      let v2 := 1 in
      let v3 := v1 + v2 in
      let v4 := v2 + v3 in
      let v5 := v4 + [v] in
      v5 + [v]
  ]
  Triple (.app prog n)
    \[]
    (fun r => \[r = (n + v + v + v + 2: Int)])
:= by
  xwp
  xstep
  xstep
  xstep
  xstep
  xstep
  xstep
  omega


example:
  forall n: Int, Triple (.app succ_using_incr n)
    \[]
    (fun r => \[r = (n + 1: Int)])
:= by
  intro n
  xwp; xsteps
  intro x p E; simp_all only []; xdisplay
  xapp (incr_spec _ _)
  -- xlet; xapp_op; xapp_op
  -- xval
  xsteps
  xsimp

example (n: Nat):
  Triple (.app factorial n)
    \[]
    (fun r => \[r = (Nat.factorial n)])
:= by
  simp
  induction n
  case zero =>
    simp [Nat.factorial]
    xwp
    xstep
    xstep
    xstep
    xsimp
  case succ n IH =>
    xwp
    xstep
    xstep
    xstep
    xapp IH
    xstep
    simp [Nat.factorial]

example {n: Int} {p: Loc}:
  let is3: Val := [slf|
    vfun x =>
      let v := !x in
      let t := v == 3 in
      if t then true else false
  ]
  Triple
    (.app is3 p)
    (p ~~> n)
    (fun r => p ~~> n ** \[r = (n == 3)])
:= by
  intro is3
  xwp
  xsteps
  xif
  . -- case true
    intro H
    simp_all
    xval; xsimp
  . -- case false
    intro H
    xval; xsimp
    exact H

-- fun
example:
  Triple [slf| [createCounter] unit ]
    \[]
    (fun f => \∃ p, (p ~~> 0) ** \[CounterSpec f p])
:= by
  xwp
  xapp_op
  intro x p E; cases E
  xfun
  intro vf H
  simp [CounterSpec]
  intro m
  apply H
  xapp (incr_spec _ _)
  xapp_op

-- fix
example (n: Int):
  Triple [slf| [createSlowAddTo] [n] ]
    \[]
    (fun f => \[SlowAddToSpec f n])
:= by
  xwp
  -- xfix; xdisplay
  xfix
  simp [SlowAddToSpec]
  intro vf Hf vx
  cases vx
  case negSucc =>
    grind
  case ofNat nx =>
    simp
    induction nx
    case zero =>
      apply Hf; xsimp
    case succ nx' IH =>
      apply Hf; xsimp; xdisplay
      xsteps
      cases nx'
      case zero =>
        specialize Hf 0 \[];
        xapp Hf
        xsteps
      case succ nx' =>
        xapp IH
        xapp_op
        omega

end XWPNotationExamples
end XTactics
