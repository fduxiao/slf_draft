namespace SLF.Map


def Map (α β: Type): Type := α → Option β


def Map.empty {α β: Type}: Map α β := fun _ => none
def Map.union {α β: Type} (m1 m2: Map α β): Map α β :=
  fun k =>
    match m1 k with
    | some v => some v
    | none => m2 k


def Map.remove {α β: Type} [DecidableEq α] (m: Map α β) (k: α): Map α β :=
  fun k' => if k = k' then none else m k'


/-!
Note that in the original book of SLF, the definition is `m k ≠ none -> k ∈ l`.
Intuitionistically, this is equivalent to `m k = none ∨ k ∈ l`.
-/
example {α: Type} (x : Option α) : x = none ∨ x ≠ none := by
  cases x <;> simp [*]


example {A B: Prop}:
  (A ∨ ¬ A) →
  ((¬ A -> B) ↔ A ∨ B)
:= by
  intro em
  apply Iff.intro
  . intro H
    cases em
    . left
      assumption
    . right
      apply H
      assumption
  . intro H
    cases H
    . intro H1
      contradiction
    . intro _
      assumption


def Map.finite {α β: Type} (m: Map α β) :=
  ∃ (l: List α), ∀ (k: α), m k = none ∨ k ∈ l


def Map.disjoint {α β: Type} (m1 m2: Map α β) :=
  ∀ (k: α), m1 k = none ∨ m2 k = none


def Map.agree {α β: Type} (m1 m2: Map α β) :=
  ∀ (k: α) (v1 v2: β), m1 k = some v1 → m2 k = some v2 → v1 = v2


def Map.mem {α β: Type} (m: Map α β) (k: α) := m k ≠ none


instance {α β: Type} : Membership α (Map α β) where
  mem := Map.mem


instance Map.dec_mem {α β: Type} {m: Map α β} {k: α}: Decidable (k ∈ m) := by
  simp [Map.mem, Membership.mem]
  cases m k
  . apply isFalse
    intro H
    apply H
    eq_refl
  . apply isTrue
    intro H
    contradiction


def Map.filter {α β: Type} (p: α → β → Bool) (m: Map α β): Map α β :=
  fun k => match m k with
    | none => none
    | some v => if p k v then some v else none


instance {α: Type} : Functor (Map α) where
  map f m := fun k =>
    match m k with
    | some v => some (f v)
    | none => none


/-!
This is not the original definition of `disjoint_eq` in SLF.
Since `∈` is decidable, we can prove the equivalence of
`∀ (k: α), k ∈ m1 → k ∈ m2 → False` and `∀ (k: α), k ∉ m1 ∨ k ∉ m2`.
-/

example {A B: Prop}:
  (A ∨ ¬ A) ->
  ((¬ A ∨ ¬ B) ↔ (A → B → False))
:= by
  intro em
  apply Iff.intro
  . intro H1 H2 H3
    cases H1
    all_goals
      rename_i H
      apply H
      assumption
  . intro H
    cases em
    . right
      apply H
      assumption
    . left
      assumption


theorem Map.disjoin_eq {α β: Type} (m1 m2: Map α β) :
  Map.disjoint m1 m2 ↔ ∀ (k: α), k ∉ m1 ∨ k ∉ m2
:= by
  simp [Map.disjoint, Membership.mem, Map.mem]


@[symm]
theorem Map.disjoint_symm {α β: Type} (m1 m2: Map α β) :
  Map.disjoint m1 m2 ↔ Map.disjoint m2 m1
:= by
  simp [Map.disjoint]
  apply Iff.intro
  . intro H k
    cases H k
    . right
      assumption
    . left
      assumption
  . intro H k
    cases H k
    . right
      assumption
    . left
      assumption


theorem Map.disjoint_comm {α β: Type} (m1 m2: Map α β) :
  Map.disjoint m1 m2 ->
  m1.union m2 = m2.union m1
:= by
  intro H
  funext k
  cases H k <;>
  . simp [Map.union, *]
    split <;> simp_all


theorem Map.union_finite {α β: Type} (m1 m2: Map α β) :
  Map.finite m1 → Map.finite m2 → Map.finite (m1.union m2)
:= by
  intro ⟨l1, H1⟩ ⟨l2, H2⟩
  unfold Map.finite
  exists (l1 ++ l2)
  intro k
  simp [Map.union]
  grind


theorem Map.remove_finite {α β: Type} [DecidableEq α] (m: Map α β) (k: α) :
  Map.finite m → Map.finite (m.remove k)
:= by
  intro ⟨l, H⟩
  unfold Map.finite
  exists l
  intro k'
  simp [Map.remove]
  grind


def FMap (α β: Type): Type := { m: Map α β // m.finite }


def FMap.mem {α β: Type} (m: FMap α β) (k: α) := m.val.mem k


instance {α β: Type} : Membership α (FMap α β) where
  mem := FMap.mem


instance FMap.dec_mem {α β: Type} {m: FMap α β} {k: α}: Decidable (k ∈ m) := Map.dec_mem
