import Qq
import SLF.Heap.Heap

namespace SLF.Heap

/-!
Another notable thing is that `simp` will always reduce a `**` expression from a tree-like structure
to a flattened list of `**` components.
-/

section ExtraTheorems
/-!
## Other theorems for building tactics
-/

@[simp, grind .]
theorem HProp.star_simpl_cancel {H1 Ha H Ht: HProp}:
  H1 ==> Ha ** Ht →
  H ** H1 ==> Ha ** H ** Ht
:= by
  grind

@[simp, grind .]
theorem HProp.qimp_unit {P Q: Unit → HProp}:
  (P ===> Q) ↔ (P () ==> Q ())
:= by
  grind

end ExtraTheorems

theorem HProp.imp_change_lhs {L L' R}:
  L = L' →
  (L ==> R ↔ L' ==> R)
:= by
  simp_all

scoped macro "himp_change_lhs" t:term ":=" p:term : tactic =>
  `(tactic| rw [HProp.imp_change_lhs (L' := (($t): HProp)) $p])

scoped macro "himp_change_lhs" t:term "at" h:ident ":=" p:term : tactic =>
  `(tactic| rw [HProp.imp_change_lhs (L' := (($t): HProp)) $p] at $h:ident)

theorem HProp.imp_change_rhs {L R R'}:
  R = R' →
  (L ==> R ↔ L ==> R')
:= by
  simp_all

scoped macro "himp_change_rhs" t:term ":=" p:term : tactic =>
  `(tactic| rw [HProp.imp_change_rhs (R' := (($t): HProp)) $p])

scoped macro "himp_change_rhs" t:term "at" h:ident ":=" p:term : tactic =>
  `(tactic| rw [HProp.imp_change_rhs (R' := (($t): HProp)) $p] at $h:ident)

example {H1 H2 H3 H4}:
  H1 = H2 →
  H2 ==> H3 →
  H3 = H4 →
  H1 ==> H4
:= by
  intro M1 M2 M3
  guard_target = H1 ==> H4
  himp_change_lhs H2 := M1
  guard_target = H2 ==> H4

  guard_hyp M2: H2 ==> H3
  himp_change_rhs _ at M2 := M3
  guard_target = H2 ==> H4

  guard_target = H2 ==> H4
  exact M2


/-!
## `xsimp` tactic for `**` expressions
-/
namespace XSimp

/--
`XSimp (Hla, Hlw, Hlt) (Hra, Hrg, Hrt)` means `Hla ** (Hlw ** Hlt) ==> (Hra ** (Hrg ** Hrt))`.

- `Hla`: _cleaned up_ items
- `Hlw`: `H1 -* H2` or `Q1 -** Q2`
- `Hlt`: items to process

- `Hra`: _cleaned up_ items
- `Hrg`: `\GC` and `\Top` on the right
- `Hrt`: items to process
-/
@[grind]
def XSimp: (HProp × HProp × HProp) → (HProp × HProp × HProp) → Prop
  | (Hla, Hlw, Hlt), (Hra, Hrg, Hrt) => Hla ** (Hlw ** Hlt) ==> (Hra ** (Hrg ** Hrt))

theorem XSimp.intro (H1 H2: HProp):
  (H1 ==> H2) ↔
  XSimp (\[], \[], H1 ** \[]) (\[], \[], H2 ** \[])
:= by
  simp [XSimp]


open Lean Meta Elab PP Tactic Qq

namespace XHelpers
/-!
Then we build some helper functions for manipulating `**` expressions.
-/


def parseProp (e: Q(Prop)): MetaM (Q(Prop)) := do
  match ← inferTypeQ e with
  | ⟨1, ~q(Prop), ~q($h)⟩ => pure q($h)
  | _ => throwError m!"{e} is not of type Prop"

def parseHProp (e: Q(HProp)): MetaM (Q(HProp)) := do
  match ← inferTypeQ e with
  | ⟨1, ~q(HProp), ~q($h)⟩ => pure q($h)
  | _ => throwError m!"{e} is not of type HProp"

def parseHPropImp (e: Q(HProp)): MetaM (Q(HProp) × Q(HProp)) := do
  match ← inferTypeQ e with
  | ⟨1, ~q(Prop), ~q($lhs ==> $rhs)⟩ => pure (q($lhs), q($rhs))
  | _ => throwError m!"{e} is not of type HProp.Imp"

def parseHPropQImp (e: Q(HProp)):
  MetaM ((u : Level) × (α : Q(Sort u)) × Q($α → HProp) × Q($α → HProp))
:= do
  match ← inferTypeQ e with
  | ⟨1, ~q(Prop), ~q(@HProp.QImp $α $lhs $rhs)⟩ => pure ⟨_, α, lhs, rhs⟩
  | _ => throwError m!"{e} is not of type HProp.QImp"

def getMainGoalType : TacticM Expr := do
  let goal ← getMainGoal
  let goalDecl ← goal.getDecl
  let goalType ← instantiateMVars goalDecl.type
  pure goalType.removeMData

def getMainGoalQ : TacticM Q(Prop) := getMainGoalType

partial def splitStar (e : Q(HProp)) : MetaM (List Q(HProp)) := do
  match e with
  | ~q($p1 ** $p2) =>
    let l1 ← splitStar p1
    let l2 ← splitStar p2
    pure (l1 ++ l2)
  | _ => pure [q($e)]

def joinStar (l : List Q(HProp)) : MetaM Q(HProp) := do
  match l with
  | [] => pure q(\[])
  | [x] => pure x
  | x :: xs =>
    let rest ← joinStar xs
    pure q($x ** $rest)

scoped elab "print_star": tactic => withMainContext do
  let goal ← getMainGoalQ
  let (lhs, rhs) ← parseHPropImp goal
  let lhs ← splitStar lhs
  let rhs ← splitStar rhs
  logInfo m!"LHS components: {lhs}"
  logInfo m!"RHS components: {rhs}"

/-!
Examples of using `print_star` tactic.
```lean
example {H1 H2 H3 H4} {n: Int}:
  H1 ** H2 ** \[n > 0] ** H3 ** H4 ==> (H1 ** H4) ** (H2 ** H3)
:= by
  print_star
  sorry
```
-/

/-!
We may frequently search for a specific component within a star conjunction and move it
to the first, thus making the following tactic.
-/
def searchFor? (P: Q(HProp) → MetaM Bool) (E: Q(HProp)) : MetaM (Option Q(HProp)) := do
  let Hs ← splitStar E
  let mut i := 0
  for h in Hs do
    if ← P h then
      break
    i := i + 1
  let ⟨left, right⟩ := Hs.splitAt i
  match right with
  | [] => pure none
  | x :: xs =>
    some <$> joinStar (x :: left ++ xs)

def searchFor! (P: Q(HProp) → MetaM Bool) (E: Q(HProp)) : MetaM Q(HProp) := do
  match ← searchFor? P E with
  | some h => pure h
  | none => pure E

section repr
def repr {α: Type} (S:α → HProp) (x:α) : HProp := S x

scoped notation:67 x " ~> " S => (repr S x)

@[app_unexpander repr]
def unexpandRepr : Lean.PrettyPrinter.Unexpander
| `($_ $S $x) => `($x ~> $S)
| _ => throw ()

theorem repr.eq {α:Type} {S:α → HProp} {x:α}:
  (x ~> S) = (S x)
:= by
  simp [repr]

def repr.Id {A:Type} (X:A) (x:A) := \[ X = x ]

end repr

end XHelpers


section ProtectAndXSimpHook
/--
`xsimp_hook` is a placeholder tactic that can be used to insert custom behavior
during the execution of `xsimp`. It does not perform any actions by itself.
-/
scoped syntax "xsimp_hook" term: tactic
/--
The default behavior of `xsimp_hook` is to fail with the message "xsimp_hook is undefined!".
Users can override this macro to insert custom behavior during the execution of `xsimp`.
-/
scoped macro_rules
  | `(tactic| xsimp_hook $_t) => `(tactic| fail "xsimp_hook is undefined!")

/--
`Protect` is a simple identity function that can be used to mark expressions
that should be protected from `xsimp`.
-/
@[grind]
def Protect {α} (x : α) : α := x

end ProtectAndXSimpHook

section XSimpStart
/-!
### `xsimp_start`
-/
open XHelpers

scoped elab "xsimpl_handle_qimpl" : tactic => withMainContext do
  -- We first get the main goal and its type
  let goal ← getMainGoalQ
  match goal with
  | ~q(@HProp.QImp $α $lhs $rhs) =>
    -- handle the implication case
    if rhs.isMVar then
      evalTactic (← `(tactic| apply HProp.qimp_refl))
    else if ← isDefEq α (Expr.const ``Unit []) then
      evalTactic (← `(tactic| rw [HProp.qimp_unit]))
    else
      evalTactic (← `(tactic| intro _ <;> unfold HProp.qstar))
  | ~q($lhs ==> $rhs) =>
    if rhs.isMVar then
      evalTactic (← `(tactic| apply HProp.imp_refl))
  | ~q(@Eq HProp $lhs $rhs) =>
    evalTactic (← `(tactic| ext))
  | ~q(@Eq (_ → HProp) $lhs $rhs) =>
    evalTactic (← `(tactic| ext))
  | _ => throwError "not a goal for xsimpl/xpull"

#try (P Q: Unit → HProp):
  P ===> Q
:= by
  have h := Nat
  xsimpl_handle_qimpl
  guard_target = P () ==> Q ()
  sorry

#try {Q1 Q2: Nat → HProp} {H2 H3}:
  Q1 *+ H2 ===> Q2 *+ H2 *+ H3
:= by
  xsimpl_handle_qimpl
  guard_target = Q1 _ ** H2 ==> (Q2 _ ** H2) ** H3
  rename_i x
  guard_target = Q1 x ** H2 ==> (Q2 x ** H2) ** H3
  sorry

#try (P Q: HProp):
  P = Q
:= by
  have h := Nat
  xsimpl_handle_qimpl
  . guard_target = P ==> Q
    sorry
  . guard_target = Q ==> P
    sorry

#try (P Q: Nat → HProp):
  P = Q
:= by
  have h := Nat
  xsimpl_handle_qimpl
  . rename_i x
    guard_target = (P x ==> Q x)
    sorry
  . rename_i x
    guard_target = (Q x ==> P x)
    sorry

scoped macro "xsimp_start" : tactic => `(tactic|
  (try simp only [HProp.star_empty_left, HProp.star_empty_right]) <;>
  intros <;>
  xsimpl_handle_qimpl <;>
  rw [XSimp.intro]
)
scoped macro "xsimp_start" "at" i:ident : tactic => `(tactic| rw [XSimp.intro] at $i:ident)

example {H1 H2 H3 H4}:
  H1 ** H2 ** H3 ** H4 ==> (H1 ** H4) ** (H2 ** H3)
:= by
  xsimp_start
  guard_target =
    XSimp
    (\[], \[], (H1 ** H2 ** H3 ** H4) ** \[])
    (\[], \[], ((H1 ** H4) ** H2 ** H3) ** \[])
  grind [XSimp]

/-!
After `xsimp_start`, we will frequently encounter `XSimp` expressions that need to be parsed and manipulated.
-/

def XHelpers.parseXSimp (e: Q(Prop)): MetaM (Q(HProp × HProp × HProp) × Q(HProp × HProp × HProp)) := do
  match e with
  | ~q(XSimp $lhs $rhs) => do
    pure (lhs, rhs)
  | _ => throwError "not an XSimp expression"

def XHelpers.parseXSimpHla (goal: Q(HProp)): MetaM Q(HProp) := do
  let ⟨lhs, _⟩ ← parseXSimp goal
  match lhs with
  | ~q(($Hla, $Hlw, $Hlt)) => pure Hla
  | _ => throwError "unexpected lhs structure"

scoped elab "print_xsimp" : tactic => do
  let goal ← getMainGoalQ
  let goal ← parseXSimp goal
  match goal with
  | (~q(($Hla, $Hlw, $Hlt)), ~q(($Hra, $Hrg, $Hrt))) => do
    logInfo m!"lhs: {Hla} ** {Hlw} ** {Hlt}"
    logInfo m!"rhs: {Hra} ** {Hrg} ** {Hrt}"
  | (lhs, rhs) => do
    logInfo m!"lhs: {lhs}"
    logInfo m!"rhs: {rhs}"

/-!
```lean
#try {H1 H2 H3 H4}:
  H1 ** H2 ** H3 ** H4 ==> (H1 ** H4) ** (H2 ** H3)
:= by
  xsimp_start
  print_xsimp
  sorry
```
-/
end XSimpStart

section XSimpHint
open XHelpers

structure Box where
  T: Type
  value: T

def Box.new {T: Type} (value: T): Box :=
  { T := T, value := value }

@[app_unexpander Box.new]
def unexpandBoxNew : Lean.PrettyPrinter.Unexpander
  | `($_ $t) => `($t)
  | _ => throw ()

inductive XHole where
  | hole : XHole

def Box.isHoleQ (b: Q(Box)): MetaM Bool := do
  match b with
  | ~q(Box.new XHole.hole) => pure true
  | _ => pure false

@[app_unexpander XHole.hole]
def unexpandXHole : Lean.PrettyPrinter.Unexpander
  | _ => `(_)

def XSimpHint := List Box deriving Inhabited

scoped syntax "xhint[" term,* "]" : term
scoped macro_rules
  | `(xhint[]) => `(([]: XSimpHint))
  | `(xhint[ $x ]) => `(([Box.new $x]: XSimpHint))
  | `(xhint[ $x, $xs,* ]) => `(([Box.new $x]: XSimpHint) ++ xhint[ $xs,* ])

partial def XSimpHint.appendQ (a b: Q(XSimpHint)): MetaM Q(XSimpHint) := do
  match a with
  | ~q([]) => pure b
  | ~q($x :: $xs) =>
    let y ← XSimpHint.appendQ xs b
    pure q($x :: $y)

def XHelpers.addXSimpHint (hint: Q(XSimpHint)): TacticM Unit :=
  liftMetaTactic fun mvarId => do
    let mvarIdNew ← mvarId.define `xsimp_hint q(XSimpHint) hint
    let (_, mvarIdNew) ← mvarIdNew.intro1P
    return [mvarIdNew]

def XHelpers.findXSimpHint?: MetaM (Option Q(XSimpHint)) := do
  let ctx ← MonadLCtx.getLCtx
  for decl in ctx do
    if decl.type == q(XSimpHint) then
      return some decl.toExpr
  return none

def XHelpers.clearXSimpHint (mustSuccess: Bool := true): TacticM Unit := do
  let ctx ← MonadLCtx.getLCtx -- get the local context.
  let mut success := false
  for decl in ctx do
    let declType := decl.type -- Find the type of the declaration.
    if declType != q(XSimpHint) then
      continue
    -- clear the decl
    success := true
    liftMetaTactic fun mvarId => do
      let mvarId ← mvarId.clear decl.fvarId
      return [mvarId]
  if !success && mustSuccess then
    throwError "no XSimpHint found to clear"

scoped elab "xsimp_hint_clear" : tactic => withMainContext do
  let goal ← getMainGoal
  let goal ← goal.getType
  if ! goal.isAppOf ``XSimp then
    XHelpers.clearXSimpHint (mustSuccess := false)

scoped elab "xsimp_hint_clear_all" : tactic => withMainContext do
  XHelpers.clearXSimpHint

def XHelpers.replaceXSimpHint (hint: Q(XSimpHint)): TacticM Unit := do
  let old ← XHelpers.findXSimpHint?
  if old.isSome then
    clearXSimpHint
  else
    pure ()
  addXSimpHint hint

def XHelpers.makeXSimpHint (ts: List Q(Box)): Q(XSimpHint) :=
  match ts with
  | [] => q([])
  | a :: b =>
    let b := XHelpers.makeXSimpHint b
    q($a :: $b)

scoped elab "xsimp_hint_put" ts:term,+ : tactic => withMainContext do
  let mut result: Array Q(Box) := Array.mk []
  for t in ts.getElems do
    let t ← match t with
      | `(_) => `(Box.new XHole.hole)
      | _ => `(Box.new $t)
    let t ← elabTerm t none
    result := result.push t
  let hint := makeXSimpHint result.toList
  let old ← XHelpers.findXSimpHint?
  match old with
  | none => XHelpers.addXSimpHint hint
  | some old =>
    let hint ← XSimpHint.appendQ old hint
    XHelpers.replaceXSimpHint <| hint

def XHelpers.findXSimpHint!: MetaM (Q(XSimpHint)) := do
  let result ← XHelpers.findXSimpHint?
  match result with
  | some r => return r
  | none => throwError "no XSimpHint found"

def XHelpers.popXSimpHint?: TacticM (Option Q(Box)) := do
  let hint ← XHelpers.findXSimpHint?
  if hint.isNone then
    return none
  let hint := hint.get!
  match hint with
  | ~q([]) => return none
  | ~q(($x :: $xs)) =>
    -- set decl to the rest of the hint
    let xs: Q(XSimpHint) := xs
    replaceXSimpHint xs
    return (some x)

def XHelpers.popXSimpHintSkipHole?: TacticM (Option Q(Box)) := do
  let hint ← XHelpers.findXSimpHint?
  if hint.isNone then
    return none
  let hint := hint.get!
  match hint with
  | ~q([]) => return none
  | ~q(($x :: $xs)) =>
    -- set decl to the rest of the hint
    let xs: Q(XSimpHint) := xs
    replaceXSimpHint xs
    if ← Box.isHoleQ x then
      return none
    else
      return (some x)

def XHelpers.popXSimpHint!: TacticM Q(Box) := do
  let hint ← XHelpers.findXSimpHint!
  match hint with
  | ~q([]) => throwError m!"xsimp_hint_next: hint is empty"
  | ~q(($x :: $xs)) =>
    -- set decl to the rest of the hint
    let xs: Q(XSimpHint) := xs
    replaceXSimpHint xs
    return x

scoped elab "xsimp_hint_next" x:term " => " t:tactic : tactic => withMainContext do
  let h ← XHelpers.popXSimpHint!
  -- I need the unexpander for `Box.new`
  let stx ← PrettyPrinter.delab h
  evalTactic <| ← match x with
  | `(_) => `(tactic| $t)
  | `($x:ident) =>
    let b ← Box.isHoleQ h
    let letT ← if b then
      `(tactic| let $x := XHole.hole)
    else
      `(tactic| let $x := $stx)
    `(tactic| $letT <;> $t <;> unfold $x at * <;> clear $x)
  | _ => throwError "unexpected pattern in xsimp_hint_next"

macro "xsimp_hint_next" " => " t:tactic : tactic => `(tactic| xsimp_hint_next _ => $t)

def XHelpers.hasNextHint : MetaM (Option Q(Box)) := do
  let old ← XHelpers.findXSimpHint?
  match old with
  | some hint =>
    match hint with
    | ~q([]) => pure none
    | ~q(($x :: $xs)) =>
      if ← Box.isHoleQ x then
        pure none
      else
        pure (some x)
  | none => pure none

scoped elab "xsimp_has_next" : tactic => withMainContext do
  if (← hasNextHint).isSome then
    pure ()
  else
    throwError m!"xsimp_has_next: no next hint available"

example:
  ∃ n, n = 3
:= by
  let h := 1
  xsimp_hint_put true, _, 3
  guard_hyp xsimp_hint :=~ xhint[true, _, 3]
  xsimp_hint_put 4, 6
  guard_hyp xsimp_hint :=~ xhint[true, _, 3, 4, 6]
  xsimp_hint_next x => skip
  guard_hyp xsimp_hint :=~ xhint[_, 3, 4, 6]
  xsimp_hint_next x => skip  -- we are able to detect holes
  xsimp_hint_next _ => skip  -- we don't need the value
  guard_hyp xsimp_hint :=~ xhint[4, 6]
  xsimp_hint_next => skip  -- or omit the variable entirely
  xsimp_hint_next => skip
  -- the hint is empty now
  guard_hyp xsimp_hint :=~ xhint[]
  fail_if_success xsimp_hint_next x => skip
  fail_if_success xsimp_has_next
  xsimp_hint_put 3
  xsimp_has_next  -- next hint is not empty
  guard_hyp xsimp_hint :=~ xhint[3]
  guard_target = ∃ n, n = 3
  xsimp_hint_next x => apply Exists.intro x
  guard_hyp xsimp_hint := xhint[]
  guard_target = 3 = 3
  xsimp_hint_clear
  rfl

end XSimpHint
