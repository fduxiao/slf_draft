namespace SLF.Map

/-!
# Map
We implement a `Map` and a `FMap` (finite map) in this file.
The `Map` is implemented as a function from `α` to `Option β`.
The `FMap` is a subtype of `Map` that is finite.
-/


/-!
## Mappoid
A class that defines the basic operations for a map-like structure.
-/

/-- A class that defines the basic operations for a map-like structure.. -/
class Mappoid (M: Type -> Type -> Type) where
  find {α β}: M α β → α → Option β
  empty {α β}: M α β
  union {α β}: M α β → M α β → M α β
  remove {α β} [DecidableEq α]: M α β → α → M α β
  filter {α β}: (α → β → Bool) → M α β → M α β


scoped notation:55 m1:55 " ∪ " m2:56 => Mappoid.union m1 m2
scoped notation:55 m1:55 " ÷ " m2:56 => Mappoid.remove m1 m2


instance {α β M} [inst: Mappoid M]: EmptyCollection (M α β) where
  emptyCollection := inst.empty

instance {α β} {M} [inst: Mappoid M]: Membership α (M α β) where
  mem m k := inst.find m k ≠ none

instance {α β M} [inst: Mappoid M]: CoeFun (M α β) (fun _ => α → Option β) where
  coe m := inst.find m


/-!
This makes sure that the `Membership` relation is decidable. We may have more
intuitively equivalent definition of properties about `Mappoid`
-/

instance {α β M} [Mappoid M] {m: M α β} {k: α}: Decidable (k ∈ m) := by
  simp [Membership.mem]
  cases m k
  . apply isFalse
    intro H
    apply H
    eq_refl
  . apply isTrue
    intro H
    contradiction

/-!
### other properties of `Mappoid`
-/

def Mappoid.disjoint {α β M} [Mappoid M] (m1 m2: M α β) :=
  ∀ (k: α), m1 k = none ∨ m2 k = none


scoped notation:50 m1:50 " ⊥ " m2:51 => Mappoid.disjoint m1 m2


def Mappoid.agree {α β M} [Mappoid M] (m1 m2: M α β) :=
  ∀ (k: α) (v1 v2: β), m1 k = some v1 → m2 k = some v2 → v1 = v2


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


theorem Mappoid.disjoin_eq {α β M} [Mappoid M] (m1 m2: M α β) :
  m1 ⊥ m2 ↔ ∀ (k: α), k ∉ m1 ∨ k ∉ m2
:= by
  simp [Mappoid.disjoint, Membership.mem]


@[symm]
theorem Mappoid.disjoint_symm {α β M} [Mappoid M] (m1 m2: M α β) :
  m1 ⊥ m2 ↔ m2 ⊥ m1
:= by
  simp [Mappoid.disjoint]
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


def Mappoid.eq {α β M} [Mappoid M] (m1 m2: M α β) :=
  ∀ (k: α), m1 k = m2 k


scoped notation:50 m1:50 " ≈ " m2:51 => Mappoid.eq m1 m2

class DisjointComm (M: Type -> Type -> Type) extends Mappoid M where
  disjoint_comm {α β} {m1 m2: M α β}:
    m1 ⊥ m2 →
    m1 ∪ m2 ≈ m2 ∪ m1


/-!
## Implementation of `Map`
-/

def Map (α β: Type): Type := α → Option β


instance {α: Type} : Functor (Map α) where
  map f m := fun k =>
    match m k with
    | some v => some (f v)
    | none => none


instance: Mappoid Map where
  find := fun m k => m k
  empty := fun _ => none
  union := fun m1 m2 k =>
    match m1 k with
    | some v => some v
    | none => m2 k
  remove := fun m k k' => if k = k' then none else m k'
  filter := fun p m k =>
    match m k with
    | none => none
    | some v => if p k v then some v else none

theorem Map.disjoint_comm {α β} {m1 m2: Map α β}:
  m1 ⊥ m2 ->
  m1 ∪ m2 ≈ m2 ∪ m1
:= by
  intro H
  unfold Mappoid.eq
  intro k
  cases H k <;>
  . simp [Mappoid.union, Mappoid.find, *] at *
    repeat split <;> simp_all


instance: DisjointComm Map where
  disjoint_comm := Map.disjoint_comm


/-!
Note that in the original book of SLF, the definition of `finite` is `m k ≠ none -> k ∈ l`.
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

/-!
We then add the `finite` property to the `Map` type,
and prove several necessary properties about `finite` maps to make the `FMap` type.
-/

def Map.finite {α β: Type} (m: Map α β) :=
  ∃ (l: List α), ∀ (k: α), m k = none ∨ k ∈ l


theorem Map.empty_finite {α β: Type} :
  (∅ : Map α β).finite
:= by
  simp [Map.finite, EmptyCollection.emptyCollection, Mappoid.empty]


theorem Map.union_finite {α β: Type} (m1 m2: Map α β) :
  m1.finite → m2.finite → (m1 ∪ m2).finite
:= by
  intro ⟨l1, H1⟩ ⟨l2, H2⟩
  unfold Map.finite
  exists (l1 ++ l2)
  intro k
  simp [Mappoid.union]
  grind


theorem Map.remove_finite {α β: Type} [DecidableEq α] (m: Map α β) (k: α) :
  Map.finite m → Map.finite (m ÷ k)
:= by
  intro ⟨l, H⟩
  unfold Map.finite
  exists l
  intro k'
  simp [Mappoid.remove]
  grind


theorem Map.filter_finite {α β: Type} (p: α → β → Bool) (m: Map α β) :
  Map.finite m → Map.finite (Mappoid.filter p m)
:= by
  intro ⟨l, H⟩
  unfold Map.finite
  exists l
  intro k
  simp [Mappoid.filter]
  grind


/-!
## Implementation of `FMap`
-/
def FMap (α β: Type): Type := { m: Map α β // m.finite }


instance: Mappoid FMap where
  find := fun m k => m.val k
  empty := ⟨∅, Map.empty_finite⟩
  union := fun m1 m2 =>
    ⟨m1.val ∪ m2.val, Map.union_finite m1.val m2.val m1.property m2.property⟩
  remove := fun m k =>
    ⟨m.val ÷ k, Map.remove_finite m.val k m.property⟩
  filter := fun p m =>
    ⟨Mappoid.filter p m.val, Map.filter_finite p m.val m.property⟩
