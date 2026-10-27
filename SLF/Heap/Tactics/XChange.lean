import SLF.Heap.Tactics.XSimp

namespace SLF.Heap.XSimp

theorem xchange_rewrite {motive: HProp → HProp} {P L P' Q}:
  motive P = L →
  P ==> P' →
  (P ==> P' → motive P ==> motive P') →
  motive P' ==> Q →
  L ==> Q
:= by
  grind

#try {H1 H2 H2' H3 H4}:
  H2 ==> H2' →
  H1 ** H2 ** H3 ==> H4
:= by
  intro H
  guard_target = H1 ** H2 ** H3 ==> H4
  apply xchange_rewrite (Q := H4) (Eq.refl _) H (by grind)
  guard_target = H1 ** H2' ** H3 ==> H4
  sorry

#try {H1 H2 H3 H4 H5}:
  H1 ** H3 ==> H5 ->
  H1 ** H2 ** H3 ==> H4
:= by
  intro H
  guard_target = H1 ** H2 ** H3 ==> H4
  apply xchange_rewrite (Q := H4) (by hprop_eq) H (motive := fun x => x ** H2) (by grind)
  guard_target = H5 ** H2 ==> H4
  sorry

#try {H1 H2 H3 H4 H5}:
  H5 ==> H1 ** H3 ->
  H2 ** H5 ==> H4
:= by
  intro H
  guard_target = H2 ** H5 ==> H4
  apply xchange_rewrite (Q := H4) (Eq.refl _) H (by grind)
  guard_target = H2 ** H1 ** H3 ==> H4
  sorry

section FindMotive
open Lean Meta Elab Tactic XHelpers Qq

def liftOption {m α} [Monad m] (o: Option α): m (Option α) := do
  match o with
  | some x => return (some x)
  | none => return none

def xchange_motive (G M: Q(HProp)): MetaM (Option Q(HProp → HProp)) := do
  let sG ← splitStar G
  let sM ← splitStar M
  let some (l1, l2) ← subtract? sG sM | return none
  let l1: Q(HProp) ← joinStar l1
  let l2: Q(HProp) ← joinStar l2
  if l1 == q(\[]) then
    if l2 == q(\[]) then
      return some q(fun x => x)
    else
      return some q(fun x => x ** $l2)
  else
    if l2 == q(\[]) then
      return some q(fun x => $l1 ** x)
    else
      return some q(fun x => $l1 ** x ** $l2)
where
  eq? (x y: Q(HProp)) : MetaM Bool := do
    let l ← isDefEq x y
    if l then
      return true
    else
      return false
  subtract? (l1 l2: List Q(HProp)): MetaM (Option ((List Q(HProp)) × (List Q(HProp)))) := do
    if l2.isEmpty then
      return some (l1, [])
    let y := l2.head!
    let mut acc: Array (Q(HProp)) := #[]
    let mut l1 := l1.toArray
    let mut found := false
    while l1.size > 0 do
      let x := l1[0]!
      if ← eq? x y then
        found := true
        l1 := l1.drop 1
        break
      else
        acc := acc.push x
        l1 := l1.drop 1
    if !found then
      return none
    for one in l2.tail! do
      let mut i := 0
      found := false
      for x in acc do
        if ← eq? x one then
          found := true
          acc := acc.eraseIdx! i
          break
        i := i + 1
      if !found then
        i := 0
        for x in l1 do
          if ← eq? x one then
            found := true
            l1 := l1.eraseIdx! i
            break
          i := i + 1
        if !found then
          return none
    return (acc.toList, l1.toList)

scoped elab "xchange_motive" M:term "is" t:term : tactic => withMainContext do
  let goal ← getMainGoalQ
  let ⟨lhs, _⟩ ← parseHPropImp goal
  let m ← elabTerm M none
  let some m ← xchange_motive lhs m | throwError "no motive found"
  let t ← elabTerm t none
  if t != m then
    throwError m!"expected motive: {t},\n but found: {m}"

scoped elab "xchange_motive" M:term: tactic => withMainContext do
  let goal ← getMainGoalQ
  let ⟨lhs, _⟩ ← parseHPropImp goal
  let m ← elabTerm M none
  let some m ← xchange_motive lhs m | throwError "no motive found"
  logInfo m!"motive is {m}"

#try {H1 H2 H2' H3 H4}:
  H2 ==> H2' →
  H1 ** H2 ** H3 ==> H4
:= by
  intro H
  xchange_motive H2 is fun x => H1 ** x ** H3
  xchange_motive H1 ** H2 is fun x => x ** H3
  sorry

#try {H1 H3 H4} (J: Int → HProp):
  J 3 ** H1 ==> J 4 →
  H1 ** J 3 ** H3 ==> H4
:= by
  intro H
  xchange_motive (J 3) is fun x => H1 ** x ** H3
  xchange_motive (J _) is fun x => H1 ** x ** H3
  xchange_motive (J _) ** H1 is fun x => x ** H3
  sorry


end FindMotive

section XChangeRewrite

open Lean Meta Elab Tactic Qq XHelpers

section Core

/--
Only display the motive and other relevant information for the rewrite.
-/
scoped elab "xchange_rewrite_try" ltr:(dir)? M:term : tactic => withMainContext do
  let ltr := match ltr with
    | some x => interpDir x
    | none => true
  let goal ← getMainGoalQ
  let ⟨lhs, rhs⟩ ← parseHPropImp goal
  -- get the type of M
  let M ← elabTerm M none
  let mut ty: Q(Prop) ← inferType M
  let (lhs', stx) ← match ty with
    | ~q($A ==> $B) => pure (A, none)
    | ~q($A = $B) =>
      if ltr then
        pure (A, some <| ← `(HProp.imp_mp))
      else
        pure (B, some <| ← `(HProp.imp_mpr))
    | _ =>
      throwError m!"unexpected type: {ty}"
  let some motive ← xchange_motive lhs lhs' | throwError m!"no motive found: {lhs} - {lhs'}"
  logInfo m!"found motive: {motive}\n"
  let motive ← PrettyPrinter.delab motive
  let rhs ← PrettyPrinter.delab rhs
  let M ← PrettyPrinter.delab M
  let stx ← match stx with
    | none => pure M
    | some x => `($x $M)
  logInfo m!"tactic is:
    apply xchange_rewrite (Q := {rhs}) (motive := {motive}) (by hprop_eq) ({stx}) (by grind)
  "

/--
This is the core tactic for rewriting heap propositions by finding the motive.
-/
scoped elab "xchange_rewrite_core" ltr:(dir)? M:term : tactic => withMainContext do
  let ltr := match ltr with
    | some x => interpDir x
    | none => true
  let goal ← getMainGoalQ
  let ⟨lhs, rhs⟩ ← parseHPropImp goal
  -- get the type of M
  let M ← elabTerm M none
  let mut ty: Q(Prop) ← inferType M
  let (lhs', stx) ← match ty with
    | ~q($A ==> $B) => pure (A, none)
    | ~q($A = $B) =>
      if ltr then
        pure (A, some <| ← `(HProp.imp_mp))
      else
        pure (B, some <| ← `(HProp.imp_mpr))
    | _ =>
      throwError m!"unexpected type: {ty}"
  let some motive ← xchange_motive lhs lhs' | throwError m!"no motive found: {lhs} - {lhs'}"
  let motive ← delabNoPP motive
  let rhs ← delabNoPP rhs
  let M ← delabNoPP M
  let stx ← match stx with
    | none => pure M
    | some x => `($x $M)
  evalTactic <|
    ← `(tactic| apply xchange_rewrite (Q := $rhs) (motive := $motive) (by hprop_eq) ($stx) ; try grind)

#try {H1 H2 H2' H3 H4}:
  H2 ==> H2' →
  H1 ** H2 ** H3 ==> H4
:= by
  intro H
  guard_target = H1 ** H2 ** H3 ==> H4
  xchange_rewrite_core H
  guard_target = H1 ** H2' ** H3 ==> H4
  sorry

#try {H1 H2 H3 H4 H5}:
  H1 ** H3 ==> H5 ->
  H1 ** H2 ** H3 ==> H4
:= by
  intro H
  guard_target = H1 ** H2 ** H3 ==> H4
  xchange_motive H1 ** H3 is fun x => x ** H2
  xchange_rewrite_core H
  guard_target = H5 ** H2 ==> H4
  sorry

#try {H1 H2 H3 H4 H5}:
  H5 ==> H1 ** H3 ->
  H2 ** H5 ==> H4
:= by
  intro H
  guard_target = H2 ** H5 ==> H4
  xchange_rewrite_core H
  guard_target = H2 ** H1 ** H3 ==> H4
  sorry

/-!
We can also use terms in `xchange_rewrite_core`
-/
#try {H1 H2 H3 H4 H5}:
  H1 ** H3 = H5 ->
  H2 ** H5 ==> H4
:= by
  intro H
  guard_target = H2 ** H5 ==> H4
  xchange_rewrite_core (HProp.imp_mpr H)
  guard_target = H2 ** H1 ** H3 ==> H4
  xchange_rewrite_core (HProp.imp_mp H)
  guard_target = H2 ** H5 ==> H4
  sorry

/-!
or use it with the `←` notation to indicate the reverse direction of the equality.
-/
#try {H1 H2 H3 H4 H5}:
  H1 ** H3 = H5 ->
  H2 ** H5 ==> H4
:= by
  intro H
  guard_target = H2 ** H5 ==> H4
  xchange_rewrite_core ← H
  guard_target = H2 ** H1 ** H3 ==> H4
  xchange_rewrite_core H
  guard_target = H2 ** H5 ==> H4
  sorry

/-!
It should be compatible with holes.
-/
#try {H1 H3 H4} (J J':Int → HProp):
  (forall n, J n ** H1 = J' (n + 1)) →
  H1 ** J 3 ** H3 ==> H4
:= by
  intro H
  guard_target = H1 ** J 3 ** H3 ==> H4
  xchange_rewrite_core H _
  guard_target = J' (3 + 1) ** H3 ==> H4
  xchange_rewrite_core ← (H _)
  guard_target = (J 3 ** H1) ** H3 ==> H4
  sorry

end Core

/-!
xchange_rewrite handle the universal quantifiers.
-/

scoped syntax "xchange_rewrite" (dir)? term : tactic
scoped elab_rules : tactic
  | `(tactic| xchange_rewrite $[$ltr]? $M) => withMainContext do
    let M' ← elabTerm M none
    let ltr: TSyntax `dir ← if ltr.isNone then `(dir| -> ) else pure ltr.get!
    let ty: Q(Prop) ← inferType M'
    evalTactic <| ← match ty with
    | ~q($A ==> $B) | ~q($C = $D) =>
      `(tactic| xchange_rewrite_core $ltr $M)
    | ~q($A ===> $B) =>
      `(tactic| xchange_rewrite_core $ltr ($M _))
    | _ =>
      if ty.isForall then
        `(tactic| xchange_rewrite $ltr ($M _))
      else
        throwError m!"xchange_rewrite does not type {ty}"

#try {H1 H3 H4} (J J':Int → HProp):
  (forall n, J n ** H1 = J' (n + 1)) →
  H1 ** J 3 ** H3 ==> H4
:= by
  intro H
  guard_target = H1 ** J 3 ** H3 ==> H4
  xchange_rewrite H  -- we can use H directly
  guard_target = J' (3 + 1) ** H3 ==> H4
  xchange_rewrite ← H -- similarly here
  guard_target = (J 3 ** H1) ** H3 ==> H4
  sorry

example {Q1 Q2 Q3: Nat → HProp}:
  Q1 ===> Q2 →
  Q2 ===> Q3 →
  forall x, Q1 x ==> Q3 x
:= by
  intro H1 H2 x
  guard_target = Q1 x ==> Q3 x
  xchange_rewrite H1
  guard_target = Q2 x ==> Q3 x
  xchange_rewrite H2
  guard_target = Q3 x ==> Q3 x
  rfl

end XChangeRewrite

section XChange

open Lean Meta Elab Tactic Qq XHelpers

scoped syntax "xchange" (dir)? term : tactic
scoped elab_rules: tactic
| `(tactic| xchange $[$ltr]? $t) => withMainContext do
  let goal ← getMainGoalQ
  let ltr: TSyntax `dir ← if ltr.isNone then `(dir| -> ) else pure ltr.get!
  evalTactic <| ← match goal with
  | ~q($A ==> $B) => `(tactic| xchange_rewrite $ltr $t)
  | ~q($C ===> $D) => `(tactic| intro h <;> (try simp) <;> xchange_rewrite $ltr $t <;> revert h)
  | _ =>
    if goal.isForall then
      `(tactic| intro h <;> xchange $ltr $t <;> revert h)
    else
      throwError "xchange only supports goals of the form `_ ==> _` or `_ ===> _`"

theorem xchange_qexit {α} {Q1 Q2: α → HProp}:
  Q1 ===> Q2 →
  (forall x, Q1 x ==> Q2 x)
:= by
  intro H
  grind

scoped macro "xchange_qexit" : tactic => `(tactic| apply xchange_qexit)

#try {H1 H3 H4} (J J':Int → HProp):
  (forall n, J n ** H1 = J' (n + 1)) →
  H1 ** J 3 ** H3 ==> H4
:= by
  intro H
  guard_target = H1 ** J 3 ** H3 ==> H4
  xchange H  -- we can use H directly
  guard_target = J' (3 + 1) ** H3 ==> H4
  xchange ← H -- similarly here
  guard_target = (J 3 ** H1) ** H3 ==> H4
  sorry

#try {H1} (J J':Int → HProp):
  (forall n, J n ** H1 = J' (n + 1)) →
  J *+ H1 ===> J'
:= by
  intro H
  guard_target = J *+ H1 ===> J'
  xchange H  -- we can use H directly
  guard_target = ∀ (h : Int), J' (h + 1) ==> J' h
  xchange ← H -- similarly here
  guard_target = ∀ (h : Int), J h ** H1 ==> J' h
  sorry

example {Q1 Q2 Q3: Nat → HProp}:
  Q1 ===> Q2 →
  Q2 ===> Q3 →
  Q1 ===> Q3
:= by
  intro H1 H2
  guard_target = Q1 ===> Q3
  xchange H1
  guard_target =~ Q2 ===> Q3
  xchange H2
  guard_target = forall h, Q3 h ==> Q3 h
  xchange_qexit
  guard_target = Q3 ===> Q3
  simp

end XChange
