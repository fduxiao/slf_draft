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

section XSimpHelpers
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
def searchFor? (P: Q(HProp) → Bool) (E: Q(HProp)) : MetaM (Option Q(HProp)) := do
  let Hs ← splitStar E
  let mut i := 0
  for h in Hs do
    if P h then
      break
    i := i + 1
  let ⟨left, right⟩ := Hs.splitAt i
  match right with
  | [] => pure none
  | x :: xs =>
    some <$> joinStar (x :: left ++ xs)

def searchFor! (P: Q(HProp) → Bool) (E: Q(HProp)) : MetaM Q(HProp) := do
  match ← searchFor? P E with
  | some h => pure h
  | none => pure E

end XSimpHelpers

section XSimpStart
/-!
### `xsimp_start`
-/

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
      evalTactic (← `(tactic| intro _))
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
  sorry

#try (P Q: HProp):
  P = Q
:= by
  have h := Nat
  xsimpl_handle_qimpl
  . sorry
  . sorry

#try (P Q: Nat → HProp):
  P = Q
:= by
  have h := Nat
  xsimpl_handle_qimpl
  . sorry
  . sorry

scoped macro "xsimp_start" : tactic => `(tactic|
  tactic_mark <;>
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
  grind [XSimp]

/-!
After `xsimp_start`, we will frequently encounter `XSimp` expressions that need to be parsed and manipulated.
-/

def parseXSimp (e: Q(Prop)): MetaM (Q(HProp × HProp × HProp) × Q(HProp × HProp × HProp)) := do
  match e with
  | ~q(XSimp $lhs $rhs) => do
    pure (lhs, rhs)
  | _ => throwError "not an XSimp expression"

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
