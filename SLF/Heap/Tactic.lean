import Qq
import SLF.Helpers
import SLF.Heap.Heap

/-!
# Tactics to simplify `HProp` expressions
-/

namespace SLF.Heap
open Map

section ac_rfl
/-!
## `ac_rfl` of `**`
-/
instance : Std.Antisymm (· ==> ·) where
  antisymm := @HProp.imp_antisym

instance : Std.Refl (· ==> ·) where
  refl := @HProp.imp_refl

instance : Std.Commutative (· ** ·) where
  comm := @HProp.star_comm

instance : Std.Associative (· ** ·) where
  assoc := @HProp.star_assoc

example {H1 H2 H3 H4}:
  H1 ** H2 ** H3 ** H4 = (H1 ** H4) ** (H2 ** H3)
:= by
  ac_rfl

open Lean.Parser.Tactic
/--
`hprop_ac_rfl` is a tactic that first simplifies all occurrences of `\[]` in `**` expressions,
and then applies `ac_rfl` to decide equality of `star` expressions.
-/
scoped syntax "hprop_rfl" (" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? : tactic

macro_rules
  | `(tactic| hprop_rfl only $[ [$[$x:term],* ] ]?) =>
    `(tactic| ((try simp only $[ [ $[$x:term],* ] ]?)) <;> first | ac_rfl | grind)
  | `(tactic| hprop_rfl $[ [$[$x:term],* ] ]?) =>
    `(tactic| ((try simp $[ [ $[$x:term],* ] ]?)) <;> first | ac_rfl | grind)
end ac_rfl

section ac_rfl_example
/-!
The following are some examples from SLF.
-/

example (H1 H2): H1 ** H2 ** \[] = H2 ** H1 ** \[] ** \[] := by
  hprop_rfl

example (H1 H2 H3 H4):
  H1 ** H2 ** \[] ** H3 ** H4 ** \[] = H4 ** H3 ** H2 ** H1 ** \[]
:= by
  hprop_rfl

example {H1 H2 H3 H}:
  H1 ** H2 ** H3 ** H = H3 ** H1 ** H2 ** H
:= by
  hprop_rfl

example {H1 H2 H3 H4 H5 H6 H7 H8 H}:
  H1 ** H2 ** H3 ** H4 ** H5 ** H6 ** H7 ** H8 ** H
  = H8 ** H1 ** H2 ** H3 ** H4 ** H5 ** H6 ** H7 ** H
:= by
  hprop_rfl
end ac_rfl_example

/-!
Another notable thing is that `simp` will always reduce a `**` expression from a tree-like structure
to a flattened list of `**` components.
-/
section
open SLF.PP

example {H1 H2 H3: HProp}:
  slf_pp (H1 ** (H2 ** H3)) = "H1 ** H2 ** H3"
  ∧
  slf_pp ((H1 ** H2) ** H3) = "(H1 ** H2) ** H3"
:= by
  simp

end

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

section XSimpLStep
/-!
### `xsimp_l_step`
A left step in the `xsimpl` process.
-/

section NecessaryTheorems
theorem XSimp.change_hla {Hla Hla' Hlw Hlt HR}:
  Hla = Hla' →
  XSimp (Hla', Hlw, Hlt) HR →
  XSimp (Hla, Hlw, Hlt) HR
:= by
  grind

def changeHla (Hs: Q(HProp)): MetaM (TSyntax `tactic) := do
  let stx ← PrettyPrinter.delab Hs
  `(tactic|
    apply XSimp.change_hla (Hla' := $stx) (by hprop_rfl [XSimp])
  )

theorem XSimp.change_hlw {Hla Hlw Hlw' Hlt HR}:
  Hlw = Hlw' →
  XSimp (Hla, Hlw', Hlt) HR →
  XSimp (Hla, Hlw, Hlt) HR
:= by
  grind

def changeHlw (Hs: Q(HProp)): MetaM (TSyntax `tactic) := do
  let stx ← PrettyPrinter.delab Hs
  `(tactic|
    apply XSimp.change_hlw (Hlw' := $stx) (by hprop_rfl [XSimp])
  )

theorem XSimp.left_flatten (Hla Hlw H1 H2 H3: HProp) R:
  XSimp (Hla, Hlw, (H1 ** H2) ** H3) R ↔
  XSimp (Hla, Hlw, H1 ** (H2 ** H3)) R
:= by
  grind

theorem XSimp.left_empty {Hla Hlw Hlt HR}:
  XSimp (Hla, Hlw, Hlt) HR →
  XSimp (Hla, Hlw, \[] ** Hlt) HR
:= by
  grind

theorem XSimp.left_pure {P Hla Hlw Hlt HR}:
  (P → XSimp (Hla, Hlw, Hlt) HR) →
  XSimp (Hla, Hlw, \[P] ** Hlt) HR
:= by
  simp [XSimp]
  intro H
  calc
    _ = \[P] ** Hla ** Hlw ** Hlt := by hprop_rfl
    _ ==> _ := by grind

theorem XSimp.left_exists {α} {J: α → HProp} {Hla Hlw Hlt HR}:
  (forall x, XSimp (Hla, Hlw, (J x ** Hlt)) HR) →
  XSimp (Hla, Hlw, \∃[J] ** Hlt) HR
:= by
  simp [XSimp]
  intro H
  calc
    _ = \∃[J] ** Hla ** Hlw ** Hlt := by grind
    _ ==> _ := by grind

theorem XSimp.left_acc_wand {H Hla Hlw Hlt HR}:
  XSimp (Hla, (H ** Hlw), Hlt) HR →
  XSimp (Hla, Hlw, (H ** Hlt)) HR
:= by
  grind

theorem XSimp.left_acc_other {H Hla Hlw Hlt HR}:
  XSimp (H ** Hla, Hlw, Hlt) HR →
  XSimp (Hla, Hlw, H ** Hlt) HR
:= by
  grind

theorem XSimp.left_keep_wand {H Hla Hlw Hlt HR}:
  XSimp (H ** Hla, Hlw, Hlt) HR →
  XSimp (Hla, H ** Hlw, Hlt) HR
:= by
  grind

theorem XSimp.left_cancel_wand_empty {H2 Hla Hlw Hlt HR} :
  XSimp (Hla, Hlw, H2 ** Hlt) HR ->
  XSimp (Hla, (\[] -* H2) ** Hlw, Hlt) HR
:= by
  grind

theorem XSimp.left_cancel_wand  {H1 H2 Hla Hlw Hlt HR}:
  XSimp (\[], Hlw, Hla ** H2 ** Hlt) HR →
  XSimp ((H1 ** Hla), (H1 -* H2) ** Hlw, Hlt) HR
:= by
  simp [XSimp]
  intro H
  calc
    _ = (H1 ** (H1 -* H2)) ** Hla ** Hlw ** Hlt := by hprop_rfl
    _ ==> H2 ** Hla ** Hlw ** Hlt := by grind
    _ ==> _ := by grind

theorem XSimp.left_cancel_wand_star  {H1 H2 H3 Hla Hlw Hlt HR}:
  XSimp (Hla, Hlw, (H2 -* H3) ** Hlt) HR →
  XSimp ((H1 ** Hla), ((H1 ** H2) -* H3) ** Hlw, Hlt) HR
:= by
  simp [XSimp]
  intro H
  calc
    _ = H1 ** ((H1 ** H2) -* H3) ** Hla ** Hlw ** Hlt := by hprop_rfl
    _ = (H1 ** (H1 -* (H2 -* H3))) ** Hla ** Hlw ** Hlt := by hprop_rfl
    _ ==> (H2 -* H3) ** Hla ** Hlw ** Hlt := by
      apply HProp.imp_frame_left
      apply HProp.wand_cancel
    _ ==> _ := by grind

theorem XSimp.left_cancel_qwand {α} (x: α) (Q1 Q2: α → HProp) Hla Hlw Hlt HR:
  XSimp (\[], Hlw, (Hla ** Q2 x ** Hlt)) HR →
  XSimp ((Q1 x ** Hla), ((Q1 -** Q2) ** Hlw), Hlt) HR
:= by
  simp [XSimp]
  intro H
  calc
    _ = (Q1 x ** (Q1 -** Q2)) ** Hla ** Hlw ** Hlt := by hprop_rfl
    _ ==> (Q1 x ** (Q1 x -* Q2 x)) ** Hla ** Hlw ** Hlt := by
      apply HProp.imp_frame_left
      apply HProp.imp_frame_right
      apply HProp.qwand_specialize
    _ ==> Q2 x ** Hla ** Hlw ** Hlt := by grind
    _ ==> _ := by grind

end NecessaryTheorems

section XSimpLStepCore

scoped elab "xsimp_step_l_core" c:bool v:bool : tactic => withMainContext do
  let cancel_wands: Bool := interpBool c
  let verbose: Bool := interpBool v
  let goal ← getMainGoalQ
  let (lhs, _rhs) ← parseXSimp goal
  evalTactic <| ← match lhs with
    | ~q(($Hla, $Hlw, ($H ** $Hlt))) =>
      match H with
      | ~q(\[]) => `(tactic| apply XSimp.left_empty)
      | ~q(\[$P]) => `(tactic| apply XSimp.left_pure <;> intro)
      | ~q($H1 ** $H2) => `(tactic| rw [XSimp.left_flatten])
      | ~q(HProp.exists $J) => `(tactic| apply XSimp.left_exists <;> intro)
      | ~q($H1 -* $H2) => `(tactic| apply XSimp.left_acc_wand)
      | ~q($H1 -** $H2) => `(tactic| apply XSimp.left_acc_wand)
      | _ => `(tactic| apply XSimp.left_acc_other)
    | ~q(($Hla, (($H1 -* $H2) ** $Hlw), \[])) =>
      match H1 with
      | ~q(\[]) => `(tactic| apply XSimp.left_cancel_wand_empty)
      | ~q($H1' ** $H1'') =>
        -- `H1' ** H1'' -* H2`
        -- We first `splitStar` `H1` into components, and find the common part with `Hla`
        let H1s ← splitStar H1
        let Hlas ← splitStar Hla
        let mut common: Option Q(HProp) := none
        for h in H1s do
          if Hlas.contains h then
            common := some h
            break
        if common.isNone then
          `(tactic| apply XSimp.left_keep_wand)
        else
          let H1' ← searchFor! (λ h => h == common.get!) H1
          let Hla' ← searchFor! (λ h => h == common.get!) Hla
          if verbose then
            if H1' != H1 then
              changeHlw q(($H1' -* $H2) ** $Hlw)
            else
              if Hla' != Hla then
                changeHla Hla'
              else
                `(tactic| apply XSimp.left_cancel_wand_star)
          else
            let t1 ← changeHlw q($H1' -* $H2 ** $Hlw)
            let t2 ← changeHla Hla'
            `(tactic| $t1 <;> $t2 <;> apply XSimp.left_cancel_wand_star)
      | _ =>
        if cancel_wands then
          let Hs ← searchFor? (λ h => h == H1) Hla
          if Hs.isNone then
            `(tactic| apply XSimp.left_keep_wand)
          else
            if verbose then
              if Hs != Hla then
                changeHla Hs.get!
              else
                `(tactic| apply XSimp.left_cancel_wand)
            else
              let t ← changeHla Hs.get!
              `(tactic| $t <;> apply XSimp.left_cancel_wand)
        else
        `(tactic| apply XSimp.left_keep_wand)
    | ~q(($Hla, (($Q1 -** $Q2) ** $Hlw), \[])) =>
      if cancel_wands then
        let Hs ← searchFor? (λ h => if h.isApp then h.appFn! == Q1 else false) Hla
        if Hs.isNone then
          `(tactic| apply XSimp.left_keep_wand)
        else
          if verbose then
            if Hs != Hla then
              changeHla Hs.get!
            else
              `(tactic| apply XSimp.left_cancel_qwand)
          else
            let t ← changeHla Hs.get!
            `(tactic| $t <;> apply XSimp.left_cancel_qwand)
      else
        `(tactic| apply XSimp.left_keep_wand)
    | _ => throwError m!"unexpected lhs structure {lhs}"

syntax "xsimp_step_l" "verbose"? (bool)? : tactic
macro_rules
  | `(tactic| xsimp_step_l verbose $b) => `(tactic| xsimp_step_l_core $b true)
  | `(tactic| xsimp_step_l $b:bool) => `(tactic| xsimp_step_l_core $b false)
  | `(tactic| xsimp_step_l verbose) => `(tactic| xsimp_step_l_core true true)
  | `(tactic| xsimp_step_l) => `(tactic| xsimp_step_l_core true false)

end XSimpLStepCore

section Examples
#try {H1 H2 H3 H4} {n: Int}:
  \[] ** H2 ** H1 ** \[n > 0] ** H3 ==> H4
:= by
  xsimp_start
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  sorry

#try {H1 H2 H3 H4} {n: Int}:
  H2 ** (\∃ x, H2) ** H1 ** \[n > 0] ** H3 ==> H4
:= by
  xsimp_start
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  sorry

#try {H1 H2 H3 H4} {n: Int}:
  H2 ** (\∃ x, \[x = 2] ** H2 ** H1 ** \[n > 0] ** H3) ==> H4
:= by
  xsimp_start
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  sorry

#try {H1 H2 H3 H4 H5}:
  H1 ** H3 = H5 →
  H1 ** H2 ** H3 ==> H4
:= by
  intro H
  sorry

/-!
`wand` and `qwand` should be canceled.
-/
#try {H1 H2 H3 H4 H5}:
  H2 ** H1 ** (H2 -* H3) ** H4 ==> H5
:= by
  xsimp_start
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  sorry

/-!
If it cannot be eliminated, it should be kept as is.
-/
#try {H1 H2 H3 H4 H5}:
  H1 ** (H2 -* H3) ** H4 ==> H5
:= by
  xsimp_start
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l -- We can no longer eliminate the wand
  -- fail_if_success xsimp_step_l
  sorry

/-!
If we have `(H2 ** H1) -* H3`, it should be canceled appropriately.
-/
#try {H1 H2 H3 H4 H5}:
  H1 ** ((H2 ** H1) -* H3) ** H4 ==> H5
:= by
  xsimp_start
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l verbose
  xsimp_step_l verbose
  xsimp_step_l verbose
  xsimp_step_l verbose
  xsimp_step_l verbose
  sorry

/-!
`qwand` should be canceled.
-/
#try {α} (v: α) (Q1 Q2: α -> HProp) H1 H2:
  (Q1 v) ** (Q1 -** Q2) ** H1  ==> H2
:= by
  xsimp_start
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l -- it cancels here
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  sorry

#try {α} (v: α) (Q1 Q2: α -> HProp) H1 H2:
  (Q1 v) ** (Q1 -** Q2) ** H1  ==> H2
:= by
  xsimp_start
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l verbose -- use verbose mode to check the state
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  sorry

end Examples
end XSimpLStep

end XSimp
