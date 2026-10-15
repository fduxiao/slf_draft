import Qq
import SLF.Heap.Heap
import SLF.Heap.Tactics.HPropEq
import SLF.Heap.Tactics.XSimpDef

namespace SLF.Heap.XSimp

section XSimpLStep

open Lean Meta Elab Tactic Qq XHelpers
/-!
### `xsimp_l_step`
A left step in the `xsimp` process.
-/

section NecessaryTheorems
theorem XSimp.change_hla {Hla Hla' Hlw Hlt HR}:
  Hla = Hla' →
  XSimp (Hla', Hlw, Hlt) HR →
  XSimp (Hla, Hlw, Hlt) HR
:= by
  grind

def XHelpers.changeHla (Hs: Q(HProp)): MetaM (TSyntax `tactic) := do
  let stx ← PrettyPrinter.delab Hs
  `(tactic|
    apply XSimp.change_hla (Hla' := $stx) (by hprop_eq [XSimp])
  )

theorem XSimp.change_hlw {Hla Hlw Hlw' Hlt HR}:
  Hlw = Hlw' →
  XSimp (Hla, Hlw', Hlt) HR →
  XSimp (Hla, Hlw, Hlt) HR
:= by
  grind

def XHelpers.changeHlw (Hs: Q(HProp)): MetaM (TSyntax `tactic) := do
  let stx ← PrettyPrinter.delab Hs
  `(tactic|
    apply XSimp.change_hlw (Hlw' := $stx) (by hprop_eq [XSimp])
  )

elab "xsimp_pick_same" t:term : tactic => withMainContext do
  let t ← elabTerm t q(HProp)
  let goal ← getMainGoalQ
  let ⟨lhs, _⟩ ← parseXSimp goal
  let ⟨Hla, _, _⟩ ← match lhs with
    | ~q(($Hla, $Hlw, $Hlt)) => pure (Hla, Hlw, Hlt)
    | _ => throwError m!"unexpected LHS structure {lhs}"
  let Hla ← searchFor? (fun stx => pure $ stx == t) Hla
  if Hla.isNone then
    throwError m!"term {t} not found in {lhs}"
  let Hla := Hla.get!
  evalTactic <| ← XHelpers.changeHla Hla

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
    _ = \[P] ** Hla ** Hlw ** Hlt := by hprop_eq
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
    _ = (H1 ** (H1 -* H2)) ** Hla ** Hlw ** Hlt := by hprop_eq
    _ ==> H2 ** Hla ** Hlw ** Hlt := by grind
    _ ==> _ := by grind

theorem XSimp.left_cancel_wand_star  {H1 H2 H3 Hla Hlw Hlt HR}:
  XSimp (Hla, Hlw, (H2 -* H3) ** Hlt) HR →
  XSimp ((H1 ** Hla), ((H1 ** H2) -* H3) ** Hlw, Hlt) HR
:= by
  simp [XSimp]
  intro H
  calc
    _ = H1 ** ((H1 ** H2) -* H3) ** Hla ** Hlw ** Hlt := by hprop_eq
    _ = (H1 ** (H1 -* (H2 -* H3))) ** Hla ** Hlw ** Hlt := by hprop_eq
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
    _ = (Q1 x ** (Q1 -** Q2)) ** Hla ** Hlw ** Hlt := by hprop_eq
    _ ==> (Q1 x ** (Q1 x -* Q2 x)) ** Hla ** Hlw ** Hlt := by
      apply HProp.imp_frame_left
      apply HProp.imp_frame_right
      apply HProp.qwand_specialize
    _ ==> Q2 x ** Hla ** Hlw ** Hlt := by grind
    _ ==> _ := by grind

end NecessaryTheorems

section XSimpLStepCore

open XHelpers

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
          let H1' ← searchFor! (λ h => pure $ h == common.get!) H1
          let Hla' ← searchFor! (λ h => pure $ h == common.get!) Hla
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
          let Hs ← searchFor? (λ h => pure $ h == H1) Hla
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
        let Hs ← searchFor? (λ h => pure $ if h.isApp then h.appFn! == Q1 else false) Hla
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
