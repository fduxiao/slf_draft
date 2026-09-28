import SLF.Lang

namespace SLF.Heap
open Lang
open Map

abbrev Heap := FMap Loc Val


def HProp := Heap → Prop
def HProp.Imp (H1 H2: HProp) : Prop := ∀ h, H1 h → H2 h

scoped notation:45 H1:45 " ==> " H2:45 => HProp.Imp H1 H2

@[refl]
theorem HProp.Imp.refl {H: HProp}: H ==> H := by
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

@[grind .]
theorem HProp.Imp.antisym {H1 H2: HProp}:
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

instance: Trans HProp.Imp HProp.Imp HProp.Imp := ⟨HProp.Imp.trans⟩


theorem HProp.Imp.op_comm {op: HProp → HProp → HProp}:
  (∀ H1 H2, op H1 H2 ==> op H2 H1) →
  ∀ H1 H2, op H1 H2 = op H2 H1
:= by
  intro A1 H1 H2
  apply antisym
  . apply A1
  . apply A1


def QImp {α} (Q1 Q2: α → HProp) : Prop := ∀ a, Q1 a ==> Q2 a
scoped notation:45 Q1:45 " ===> " Q2:45 => QImp Q1 Q2

@[refl]
theorem QImp.refl {α} {Q: α → HProp}:
  Q ===> Q
:= by
  intro a
  rfl


def HProp.empty : HProp := fun h => h = ∅
def HProp.single (p: Loc) (v: Val): HProp := fun h => h = Mappoid.single p v
def HProp.star (H1 H2: HProp): HProp :=
  fun h =>
    ∃ h1 h2, H1 h1 ∧ H2 h2 ∧ h1 ⊥ h2 ∧ h = h1 ∪ h2
def HProp.exists {α} (Q: α → HProp): HProp :=
  fun h => ∃ a, Q a h
def HProp.forall {α} (Q: α → HProp): HProp :=
  fun h => ∀ a, Q a h

-- notations
scoped notation "emp" => HProp.empty
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

scoped syntax:59 "∃' " binder+ ", " term:51: term
scoped syntax:59 "∀' " binder+ ", " term:51: term
macro_rules
  | `(∃' $b, $Q) => `(HProp.exists ([fun $b | $Q]))
  | `(∃' $b $[$b']*, $Q) => `(HProp.exists ([fun $b | ∃' $[$b']*, $Q]))
  | `(∀' $b, $Q) => `(HProp.forall ([fun $b | $Q]))
  | `(∀' $b $[$b']*, $Q) => `(HProp.forall ([fun $b | ∀' $[$b']*, $Q]))


@[app_unexpander HProp.exists]
def HProp.exists.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $Q) =>
    match Q with
    | `(∃' $y*, $Q') => `(∃' $x:ident $y*, $Q')
    | _ => `(∃' $x:ident, $Q)
  | _ => throw ()


@[app_unexpander HProp.forall]
def HProp.forall.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $Q) =>
    match Q with
    | `(∀' $y*, $Q') => `(∀' $x:ident $y*, $Q')
    | _ => `(∀' $x:ident, $Q)
  | _ => throw ()


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
  (∃' n, H1 n) = HProp.exists fun n => H1 n
:= by
  rfl
example (H1: Nat -> Nat → HProp):
  ∃' n1 n2, H1 n1 n2 = ∃' n1, ∃' n2, H1 n1 n2
:= by
  rfl
example (H1: Nat → HProp) (H2: HProp):
  ∃' n, (H1 n ** H2) = ∃' n, H1 n ** H2
:= rfl
example (H1: Nat → HProp) (H2: HProp):
  (∃' n, H1 n) ** H2 = (∃' n, H1 n).star H2
:= rfl


def HProp.pure (P: Prop) : HProp := ∃' (_: P), emp
def HProp.top : HProp := ∃' (H: HProp), H
def HProp.wand (H1 H2: HProp): HProp := ∃' (H0: HProp), H0 ** HProp.pure ((H1 ** H0) ==> H2)
def HProp.qwand {α} (Q1 Q2: α → HProp): HProp :=
  ∀' x, HProp.wand (Q1 x) (Q2 x)

@[simp]
theorem HProp.pure.simp {P h}: HProp.pure P h ↔ P ∧ h = ∅ := by
  simp [HProp.pure, HProp.exists, HProp.empty]


@[simp]
theorem HProp.top.simp {h}: HProp.top h := by
  simp [HProp.top, HProp.exists]
  exists (fun h => True)

notation:100 "pure[" P "]" => HProp.pure P
notation "⊤" => HProp.top
notation:60 Q:60 " *+ " H:61 => (fun x => (Q x) ** H)
notation:57 H1:57 " -* " H2:57 => HProp.wand H1 H2
notation:57 Q1:57 " --* " Q2:58 => HProp.qwand Q1 Q2
