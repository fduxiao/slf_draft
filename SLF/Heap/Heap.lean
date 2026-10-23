import SLF.Lang

namespace SLF.Heap
open Lang
open Map

abbrev Heap := FMap Loc Val

theorem Heap.exists_refresh (m: Heap) (null: Loc := 0):
  ∃ (n: Loc), n ∉ m ∧ n ≠ null
:= FMap.exists_refresh

theorem Heap.single_refresh (m: Heap) (null: Loc := 0) (v):
  ∃ (x: Loc), ∅[x => v] ⊥ m ∧ x ≠ null
:= FMap.single_refresh

@[grind]
def HProp := Heap → Prop

section Imp

@[grind]
def HProp.Imp (H1 H2: HProp) : Prop := ∀ h, H1 h → H2 h

scoped notation:45 H1:45 " ==> " H2:45 => HProp.Imp H1 H2

@[simp, refl, grind .]
theorem HProp.imp_refl {H: HProp}: H ==> H := by
  intro h hH
  exact hH

@[grind .]
theorem HProp.Imp.trans {H1 H2 H3: HProp}:
  H1 ==> H2 →
  H2 ==> H3 →
  H1 ==> H3
:= by
  intro h12 h23
  intro h h1
  specialize h12 h
  specialize h23 h
  apply h23 (h12 h1)

abbrev HProp.imp_trans {H1 H2 H3: HProp}:
  H1 ==> H2 →
  H2 ==> H3 →
  H1 ==> H3
:= HProp.Imp.trans

instance: Trans HProp.Imp HProp.Imp HProp.Imp := ⟨HProp.imp_trans⟩
instance: Trans (@Eq HProp) HProp.Imp HProp.Imp := Trans.mk $ by simp_all
instance: Trans HProp.Imp (@Eq HProp) HProp.Imp := Trans.mk $ by simp_all

@[grind ., ext]
theorem HProp.imp_antisym {H1 H2: HProp}:
  H1 ==> H2 →
  H2 ==> H1 →
  H1 = H2
:= by
  intro h12 h21
  funext h
  specialize h12 h
  specialize h21 h
  apply propext
  constructor
  . exact h12
  . exact h21

@[grind .]
theorem HProp.imp_mp {H1 H2: HProp}:
  H1 = H2 →
  H1 ==> H2
:= by
  grind

@[grind .]
theorem HProp.imp_mpr {H1 H2: HProp}:
  H1 = H2 →
  H2 ==> H1
:= by
  grind

@[symm]
theorem HProp.imp_op_comm {op: HProp → HProp → HProp}:
  (∀ H1 H2, op H1 H2 ==> op H2 H1) →
  ∀ H1 H2, op H1 H2 = op H2 H1
:= by
  intro A1 H1 H2
  apply imp_antisym
  . apply A1
  . apply A1

theorem HProp.imp_apply {H1 H2: HProp} {h}:
  H1 h →
  H1 ==> H2 →
  H2 h
:= by
  intro h1 h12
  exact h12 h h1

end Imp

section QImp
@[grind]
def HProp.QImp {α} (Q1 Q2: α → HProp) : Prop := ∀ a, Q1 a ==> Q2 a
scoped notation:45 Q1:45 " ===> " Q2:45 => HProp.QImp Q1 Q2

@[simp,refl, grind .]
theorem HProp.qimp_refl {α} {Q: α → HProp}:
  Q ===> Q
:= by
  intro a
  rfl
end QImp

section HPropOp
@[grind]
def HProp.empty : HProp := fun h => h = ∅
@[grind]
def HProp.single (p: Loc) (v: Val): HProp := fun h => h = Mappoid.single p v
@[grind]
def HProp.star (H1 H2: HProp): HProp :=
  fun h =>
    ∃ h1 h2, H1 h1 ∧ H2 h2 ∧ h1 ⊥ h2 ∧ h = h1 ∪ h2
@[grind]
def HProp.exists {α} (Q: α → HProp): HProp :=
  fun h => ∃ a, Q a h
@[grind]
def HProp.forall {α} (Q: α → HProp): HProp :=
  fun h => ∀ a, Q a h

open Lean TSyntax.Compat
-- notations
scoped notation "\\[]" => HProp.empty
scoped notation:68 p " ~~> " v:68 => HProp.single p v
scoped notation:59 H1:59 " ** " H2:59 => HProp.star H1 H2
declare_syntax_cat binder (behavior := symbol)
scoped syntax ident (":" term)? : binder
scoped syntax "_" (":" term)? : binder
scoped syntax " (" binder ") " : binder
scoped syntax "[fun" binder "|" term "]" : term
macro_rules
  | `([fun $b:ident | $Q]) => `(fun $b => $Q)
  | `([fun $b:ident : $t | $Q]) => `(fun $b : $t => $Q)
  | `([fun _ | $Q]) => `(fun _ => $Q)
  | `([fun _ : $t | $Q]) => `(fun _ : $t => $Q)
  | `([fun ($b: binder) | $Q]) => `([fun $b | $Q])

scoped syntax "\\∃[" term "]": term
scoped syntax "\\∀[" term "]": term
scoped syntax:59 "\\∃ " explicitBinders", " term:51: term
scoped syntax:59 "\\∀ " explicitBinders ", " term:51: term
macro_rules
  | `(\∃[ $a ]) => `(HProp.exists $a)
  | `(\∃ $b, $Q) => expandExplicitBinders ``HProp.exists b Q
  | `(\∀[ $a ]) => `(HProp.forall $a)
  | `(\∀ $b, $Q) => expandExplicitBinders ``HProp.forall b Q


@[app_unexpander HProp.exists]
def HProp.exists.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $Q) =>
    match Q with
    | `(\∃ $[$y:ident]*, $Q') => `(\∃ $x:ident $[$y:ident]*, $Q')
    | _ => `(\∃ $x:ident, $Q)
  | _ => throw ()

#try {p q H1}:
  H1 ==> \∃ (n m: Int), (p ~~> n ** q ~~> m)
:= by
  sorry

@[app_unexpander HProp.forall]
def HProp.forall.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $Q) =>
    match Q with
    | `(\∀ $[$y:ident]*, $Q') => `(\∀ $x:ident $[$y:ident]*, $Q')
    | _ => `(\∀ $x:ident, $Q)
  | _ => throw ()

section Examples
example (H1 H2 H3: HProp): H1 ** H2 ** H3 = H1 ** (H2 ** H3) := rfl
example (H1 H2 H3: HProp): (H1 ** H2) ** H3 = (H1 ** H2) ** H3 := rfl
example (p: Loc) (v: Val): p ~~> v = HProp.single p v := rfl
example (p: Loc) (v: Val) (H: HProp):
  p ~~> v ** H = (HProp.single p v).star H
:= rfl
example (p: Loc) (v: Val) (H: HProp):
  H ** p ~~> v = H.star (HProp.single p v)
:= rfl

example (H1: Nat → HProp):
  (\∃ n, H1 n) = HProp.exists fun n => H1 n
:= by
  rfl
example (H1: Nat -> Nat → HProp):
  \∃ n1 n2, H1 n1 n2 = \∃ n1, \∃ n2, H1 n1 n2
:= by
  rfl
example (H1: Nat -> Nat → HProp):
  \∃ (n1 n2: Nat), H1 n1 n2 = \∃ n1: Nat, \∃ n2: Nat, H1 n1 n2
:= by
  rfl
example (H1: Nat → HProp) (H2: HProp):
  \∃ n, (H1 n ** H2) = \∃ n, H1 n ** H2
:= rfl
example (H1: Nat → HProp) (H2: HProp):
  (\∃ n, H1 n) ** H2 = (\∃ n, H1 n).star H2
:= rfl
end Examples

@[grind]
def HProp.pure (P: Prop) : HProp := \∃ (_: P), \[]
@[grind]
def HProp.top : HProp := \∃ (H: HProp), H
@[grind]
def HProp.wand (H1 H2: HProp): HProp := \∃ H0, H0 ** HProp.pure ((H1 ** H0) ==> H2)
@[grind]
def HProp.qwand {α} (Q1 Q2: α → HProp): HProp := \∀ x, HProp.wand (Q1 x) (Q2 x)
@[grind, simp]
def HProp.qstar {α} (Q: α → HProp) (H: HProp): α → HProp := (fun x => (Q x) ** H)
@[simp, grind =]
theorem HProp.pure.simp {P h}: HProp.pure P h ↔ P ∧ h = ∅ := by
  simp [HProp.pure, HProp.exists, HProp.empty]

notation "\\[" P "]" => HProp.pure P
notation "\\Top" => HProp.top
notation:60 Q:60 " *+ " H:61 => HProp.qstar Q H
notation:57 H1:57 " -* " H2:57 => HProp.wand H1 H2
notation:57 Q1:57 " -** " Q2:58 => HProp.qwand Q1 Q2

end HPropOp

section HPropProperties
/-!
# Properties of `HProp`
-/
section Empty
/-!
## Properties of `HProp.empty`
-/
@[simp, grind .]
theorem HProp.empty_intro:
  \[] ∅
:= by
  simp [HProp.empty]

@[simp, grind .]
theorem HProp.empty_elim {h}:
  \[] h = (h = ∅)
:= by
  simp [HProp.empty]

end Empty
section Star
/-!
## Properties of `HProp.star`
-/
@[simp, grind .]
theorem HProp.star_intro {H1 H2: HProp} {h1 h2}:
  H1 h1 →
  H2 h2 →
  h1 ⊥ h2 →
  (H1 ** H2) (h1 ∪ h2)
:= by
  simp [HProp.star]
  grind

@[simp, grind .]
theorem HProp.star_elim {H1 H2: HProp} {h}:
  (H1 ** H2) h →
  ∃ h1 h2, H1 h1 ∧ H2 h2 ∧ h1 ⊥ h2 ∧ h = h1 ∪ h2
:= by
  simp [HProp.star]

@[simp, grind =]
theorem HProp.star_assoc (H1 H2 H3: HProp):
  (H1 ** H2) ** H3 = H1 ** (H2 ** H3)
:= by
  funext h
  simp [HProp.star]
  grind

@[simp, symm, grind =]
theorem HProp.star_comm (H1 H2: HProp):
  H1 ** H2 = H2 ** H1
:= by
  funext h
  simp [HProp.star]
  grind

@[simp, grind =]
theorem HProp.star_empty_left (H: HProp):
  \[] ** H = H
:= by
  funext h
  simp [HProp.star, HProp.empty]
  grind

@[simp, grind =]
theorem HProp.star_empty_right (H: HProp):
  H ** \[] = H
:= by
  funext h
  simp [HProp.star, HProp.empty]
  grind

@[simp, grind =]
theorem HProp.star_exists {α} {J: α → HProp} {H: HProp}:
  \∃[J] ** H = \∃ x, J x ** H
:= by
  funext h
  simp [HProp.exists, HProp.star]
  grind

@[simp, grind .]
theorem HProp.star_forall' {α} {J: α → HProp} {H: HProp}:
  \∀[J] ** H ==> \∀[J *+ H]
:= by
  unfold HProp.star HProp.forall HProp.Imp HProp.qstar
  grind

@[simp, grind .]
theorem HProp.imp_frame_left {H2 H1 H1': HProp}:
  H1 ==> H1' →
  H1 ** H2 ==> H1' ** H2
:= by
  unfold HProp.star HProp.Imp
  grind

@[simp, grind .]
theorem HProp.imp_frame_right {H1 H2 H2': HProp}:
  H2 ==> H2' →
  H1 ** H2 ==> H1 ** H2'
:= by
  unfold HProp.star HProp.Imp
  grind

theorem HProp.imp_frame_counterexample:
  let H1 : HProp := 0 ~~> [slf| unit]
  let H2 : HProp := 0 ~~> [slf| unit]
  let H3 : HProp := \[False]
  H1 ** H2 ==> H1 ** H3 ∧ ¬ (H2 ==> H3)
:= by
  intro H1 H2 H3
  and_intros
  · intro h hstar
    simp [HProp.star, H3]
    obtain ⟨h1, h2, H1h1, H2h2, hdisjoint, E⟩ := hstar
    simp [H1, H2, HProp.single] at H1h1 H2h2
    subst h1 h2
    clear H1 H2 H3 h E
    rewrite [FMap.disjoint_single_single] at hdisjoint
    contradiction
  · intro hImp
    specialize hImp ∅[ 0 => [slf| unit ]]
    simp [H2, H3, HProp.single] at hImp

@[simp, grind .]
theorem HProp.imp_frame_lr {H1 H1' H2 H2': HProp}:
  H1 ==> H1' →
  H2 ==> H2' →
  H1 ** H2 ==> H1' ** H2'
:= by
  unfold HProp.star HProp.Imp
  grind

@[simp, grind .]
theorem HProp.imp_star_trans_left {H1 H2 H3 H4: HProp}:
  H1 ==> H2 →
  H2 ** H3 ==> H4 →
  H1 ** H3 ==> H4
:= by
  unfold HProp.star HProp.Imp
  grind

@[simp, grind .]
theorem HProp.imp_star_trans_right {H1 H2 H3 H4: HProp}:
  H1 ==> H2 →
  H3 ** H2 ==> H4 →
  H3 ** H1 ==> H4
:= by
  grind

end Star
section Pure
/-!
## Properties of `HProp.pure`
-/
@[simp, grind .]
theorem HProp.pure_intro {P}:
  P → \[P] ∅
:= by
  simp [HProp.pure, HProp.exists]

@[grind .]
theorem HProp.pure_elim {P} {h}:
  \[P] h → P ∧ h = ∅
:= by
  simp [HProp.pure, HProp.exists]

@[simp, grind =]
theorem HProp.star_pure_left {P} {H: HProp} {h}:
  (\[P] ** H) h = (P ∧ H h)
:= by
  simp [HProp.star, HProp.pure, HProp.exists]
  grind

@[simp, grind =]
theorem HProp.star_pure_right {P} {H: HProp} {h}:
  (H ** \[P]) h = (H h ∧ P)
:= by
  simp [HProp.star, HProp.pure, HProp.exists]
  grind

@[simp, grind .]
theorem HProp.imp_star_pure_right {P} {H H'}:
  P →
  (H ==> H') →
  H ==> (\[P] ** H')
:= by
  simp [HProp.star, HProp.Imp, HProp.pure, HProp.exists]
  grind

@[simp, grind =]
theorem HProp.pure_empty {P} h:
 \[P] h = (P ∧ h = ∅)
:= by
  simp [HProp.pure, HProp.exists]

@[simp, grind .]
theorem HProp.imp_empty_pure {P}:
  P → \[] ==> \[P]
:= by
  intro H h
  grind

@[simp, grind .]
theorem HProp.imp_star_pure_left {P} {H H'}:
  (\[P] ** H) ==> H' ↔
  (P → (H ==> H'))
:= by
  simp [HProp.star, HProp.Imp, HProp.pure, HProp.exists]
  grind

@[simp, grind .]
theorem HProp.imp_star_pure_left' {P} {H H'}:
  (H ** \[P]) ==> H' ↔
  (P → (H ==> H'))
:= by
  simp [HProp.star, HProp.Imp, HProp.pure, HProp.exists]
  grind

@[simp, grind =]
theorem HProp.empty_eq_pure_true:
  \[True] = \[]
:= by
  ext h <;> grind

@[simp, grind =]
theorem HProp.false_star_any {H}:
  \[False] ** H = \[False]
:= by
  ext h <;> grind

@[simp, grind =]
theorem HProp.false_star_any' {H}:
  H ** \[False] = \[False]
:= by
  grind
end Pure

section Exists
/-!
## Properties of `HProp.exists`
-/

theorem HProp.exists_intro {α} {x: α} {J: α → HProp} {h}:
  J x h → \∃[J] h
:= by
  simp [HProp.exists]
  grind

@[simp]
theorem HProp.exists_elim' {α} {J: α → HProp} {x: α}:
  J x ==> \∃[J]
:= by
  simp [HProp.exists, HProp.Imp]
  grind

@[simp, grind =]
theorem HProp.exists_elim {α} {J: α → HProp} {h}:
  \∃[J] h = ∃ x, J x h
:= by
  simp [HProp.exists]

@[simp, grind .]
theorem HProp.imp_exists_left {α} {J: α → HProp} {H: HProp}:
  \∃[J] ==> H ↔ ∀ x, J x ==> H
:= by
  simp [HProp.exists, HProp.Imp]
  grind

@[simp]
theorem HProp.imp_exists_right {α} {J: α → HProp} {H: HProp} {x}:
  (H ==> J x) → H ==> \∃[J]
:= by
  simp [HProp.exists, HProp.Imp]
  grind

@[simp]
theorem HProp.imp_exists {α} {J1 J2: α → HProp}:
  J1 ===> J2 →
  \∃[J1] ==> \∃[J2]
:= by
  simp [HProp.exists, HProp.Imp, HProp.QImp]
  grind

end Exists
section Forall
/-!
## Properties of `HProp.forall`
-/
@[simp, grind =]
theorem HProp.forall_spec {α} {J: α → HProp} {h}:
  (\∀[J]) h ↔ ∀ x, J x h
:= by
  simp [HProp.forall]

theorem HProp.forall_right {α} {J: α → HProp} {H: HProp}:
  (∀ x, H ==> J x) ↔
  H ==> \∀[J]
:= by
  simp [HProp.forall, HProp.Imp]
  grind

theorem HProp.forall_left {α} {J: α → HProp} {H: HProp} {x}:
  J x ==> H →
  \∀[J] ==> H
:= by
  simp [HProp.forall, HProp.Imp]
  grind

theorem HProp.forall_specialize {α} {J: α → HProp} {h} {x: α}:
  (\∀[J]) h → J x h
:= by
  simp [HProp.forall]
  grind

theorem HProp.imp_forall {α} {J1 J2: α → HProp}:
  J1 ===> J2 →
  \∀[J1] ==> \∀[J2]
:= by
  simp [HProp.forall, HProp.Imp, HProp.QImp]
  grind

end Forall
section Wand
/-!
## Properties of `HProp.wand`
-/
@[simp, grind =]
theorem HProp.wand_eval {H1 H2: HProp} {h}:
  (H1 -* H2) h = ∃ H0, H0 h ∧ H0 ** H1 ==> H2
:= by
  simp [HProp.wand]

@[simp, grind =]
theorem HProp.wand_equiv {H0 H1 H2: HProp}:
  (H0 ==> H1 -* H2) ↔ (H0 ** H1 ==> H2)
:= by
  apply Iff.intro
  . rintro H h ⟨h1, h2, H0h1, H1h2, HD, E⟩
    obtain ⟨H', K⟩ := H h1 H0h1
    simp_all
    obtain ⟨K1, K2⟩ := K
    apply K2
    exists h2, h1
    simp_all
    grind
  . rintro H h H0h
    simp [HProp.wand, HProp.exists]
    exists H0
    simp_all

@[simp, grind .]
theorem HProp.wand_cancel {H1 H2: HProp}:
  H1 ** (H1 -* H2) ==> H2
:= by
  intro h H
  obtain ⟨h1, h2, H1h1, H12h2, HD, E⟩ := H
  simp at H12h2
  obtain ⟨H0, H0h2, I⟩ := H12h2
  apply I
  exists h1, h2

@[simp, grind .]
theorem HProp.wand_cancel_counterexample:
  let H1 : HProp := 0 ~~> [slf| unit]
  let H2 : HProp := \[]
  let H3 : HProp := \[False]
  H1 ** (H1 -* H2) ==> H3 ∧ ¬ H2 ==> H3
:= by
  intro H1 H2 H3
  and_intros
  · intro h hstar
    simp [H3]
    have hEmp : H2 h := HProp.wand_cancel h hstar
    simp [H2] at hEmp
    obtain ⟨h1, h2, hH1, _, _, _⟩ := hstar
    simp_all
    simp [H1, HProp.single] at hH1
    have hMem : 0 ∈ h1 ∪ h2 := by
      apply FMap.mem_union_left
      simp_all
    rw [hEmp] at hMem
    simp at hMem
  · intro hImp
    specialize hImp ∅
    simp [H2] at hImp
    simp [H3, HProp.pure] at hImp

example:
  ∃ H1 H2 H3 H, H1 ** ((H1 ** H2) -* H3) ==> H ∧ ¬ (H2 -* H3) ==> H
:= by
  let H1 : HProp := 0 ~~> [slf| unit]
  let H2 : HProp := \[]
  let H3 : HProp := \[]
  let H : HProp := \[False]
  exists H1, H2, H3, H
  simp [H2]
  grind

@[simp, grind .]
theorem HProp.imp_empty_wand_same {H: HProp}:
  \[] ==> (H -* H)
:= by
  intro h K
  simp_all
  exists \[]
  simp

@[simp, grind =]
theorem HProp.wand_empty_left {H: HProp}:
  (\[] -* H) = H
:= by
  ext h K
  . simp at K
    obtain ⟨H0, H0h, I⟩ := K
    apply I
    exact H0h
  . simp
    exists H

@[simp, grind =]
theorem HProp.wand_pure_left {P H}:
  P → (\[P] -* H) = H
:= by
  grind

@[simp, grind =]
theorem HProp.wand_curry_eq {H1 H2 H3: HProp}:
  (H1 ** H2) -* H3 = H1 -* (H2 -* H3)
:= by
  ext h K
  . simp at K
    obtain ⟨H0, H0h, E⟩ := K
    simp
    exists H0
    simp_all
    grind
  . grind

@[grind .]
theorem HProp.wand_inv {H1 H2 h1 h2}:
  (H1 -* H2) h2 →
  H1 h1 →
  h1 ⊥ h2 →
  H2 (h1 ∪ h2)
:= by
  intro H12 h1h HD
  simp at H12
  obtain ⟨H0, H0h2, I⟩ := H12
  apply I
  grind

end Wand
section QWand
/-!
## Properties of `HProp.qwand`
-/
@[simp, grind=]
theorem HProp.qwand_eval {α} {Q1 Q2: α → HProp} {h}:
  (Q1 -** Q2) h = (\∀ x, Q1 x -* Q2 x) h
:= by
  simp [HProp.qwand]

@[simp, grind =]
theorem HProp.qwand_eq {α} {Q1 Q2: α → HProp} {H: HProp}:
   H ==> (Q1 -** Q2) ↔ (Q1 *+ H) ===> Q2
:= by
  apply Iff.intro
  . intro K a
    simp
    rintro h ⟨h1, h2, Hh1, Q1ah2, HD, E⟩
    specialize K h1 Hh1 a
    simp at K
    obtain ⟨H0, H0h1, I⟩ := K
    apply I
    exists h1, h2
  . intro K h Hh a
    specialize K a
    simp_all
    exists H

@[simp, grind .]
theorem HProp.qwand_cancel {α} {Q1 Q2: α → HProp}:
  Q1 *+ (Q1 -** Q2) ===> Q2
:= by
  rewrite [<-HProp.qwand_eq]
  simp

theorem HProp.qwand_specialize {α} {Q1 Q2: α → HProp} {x}:
  (Q1 -** Q2) ==> (Q1 x -* Q2 x)
:= by
  intro h K
  specialize K x
  exact K

end QWand
section HTop
/-!
## Properties of `HProp.HTop`
-/
@[simp, grind .]
theorem HProp.top.simp {h}: HProp.top h := by
  simp [HProp.top, HProp.exists]
  exists (fun h => True)

@[simp, grind .]
theorem HProp.top_terminal {H: HProp}:
  H ==> HProp.top
:= by
  intro h K
  simp

@[simp, grind =]
theorem HProp.exists_self_top:
  \∃ H, H = \Top
:= by
  simp [HProp.top]

@[simp, grind =]
theorem HProp.star_top_top:
  \Top ** \Top = \Top
:= by
  ext h K
  . grind
  . simp [HProp.star]
    exists h, ∅
    simp

end HTop
section Single

/-!
## Properties of `HProp.single`
-/
@[simp, grind .]
theorem HProp.single_intro {p v}:
  (p ~~> v) ∅[p => v]
:= by
  simp [HProp.single]

@[simp, grind =]
theorem HProp.single_eval {p v} {h}:
  (p ~~> v) h = (h = ∅[p => v])
:= by
  simp [HProp.single]

@[simp, grind =]
theorem HProp.star_single_same_location {p w1 w2}:
  (p ~~> w1) ** (p ~~> w2) = \[False]
:= by
  ext h K
  . grind
  . grind

end Single

section Affine

def HProp.affine (_: HProp) := True

@[simp, grind .]
theorem HProp.affine_any {H: HProp}:
  affine H
:= by
  simp [HProp.affine]

@[simp, grind .]
theorem HProp.affine_empty:
  HProp.affine \[] :=
by
  simp [HProp.affine]

@[simp, grind .]
theorem HProp.affine_pure {P}:
  HProp.affine \[P]
:= by
  grind

@[simp, grind .]
theorem HProp.affine_star {H1 H2}:
  HProp.affine H1 →
  HProp.affine H2 →
  HProp.affine (H1 ** H2)
:= by
  grind

@[simp, grind .]
theorem HProp.affine_exists {α} {J:α → HProp}:
  (∀ x, HProp.affine (J x)) →
  HProp.affine (\∃ x, (J x))
:= by
  grind

@[simp, grind .]
theorem HProp.affine_forall {α} {J:α → HProp}:
  (∀ x, HProp.affine (J x)) →
  HProp.affine (\∀ x, (J x))
:= by
  grind

@[simp, grind .]
theorem HProp.affine_star_pure {P H}:
  (P → HProp.affine H) →
  HProp.affine (\[P] ** H)
:= by
  grind

section GC

@[grind]
def HProp.gc := HProp.top /- equivalent to \∃ H, \[affine H] ** H -/

@[grind =]
theorem HProp.gc_equiv:
  HProp.gc = \Top
:= by
  simp [HProp.gc]

scoped notation "\\GC" => (HProp.gc)

@[app_unexpander HProp.gc]
def unexpandHPropGc : Lean.PrettyPrinter.Unexpander
  | `($_) => `(\GC)

@[grind =]
theorem HProp.gc_simp:
  \GC = \Top
:= by
  simp [HProp.gc]
end GC

@[simp, grind =]
theorem HProp.gc_eq_exists:
  \∃ H, \[affine H] ** H = \GC
:= by
  simp [HProp.gc]

@[simp, grind .]
theorem HProp.affine_gc :
  HProp.affine \GC
:= by
  simp [HProp.affine]

@[simp, grind .]
theorem HProp.imp_gc_r {H: HProp}:
  H.affine →
  H ==> \GC
:= by
  intro h K
  simp [HProp.gc]

@[simp, grind =]
theorem HProp.star_gc_gc:
  \GC ** \GC = \GC
:= by
  simp [HProp.gc]
end Affine
end HPropProperties
