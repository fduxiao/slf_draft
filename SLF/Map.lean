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
  single {α β} [DecidableEq α]: α → β → M α β
  remove {α β} [DecidableEq α]: M α β → α → M α β
  filter {α β}: (α → β → Bool) → M α β → M α β

instance {α β M} [inst: Mappoid M]: EmptyCollection (M α β) where
  emptyCollection := inst.empty

instance {α β} {M} [inst: Mappoid M]: Membership α (M α β) where
  mem m k := inst.find m k ≠ none

instance {α β M} [inst: Mappoid M]: CoeFun (M α β) (fun _ => α → Option β) where
  coe m := inst.find m

instance {α β M} [inst: Mappoid M]: GetElem? (M α β) α β (fun m k => k ∈ m) where
  getElem m k h := by
    cases E: m k with
    | some v => exact v
    | none => contradiction

  getElem? := inst.find


instance {α β M} [inst: Mappoid M]: Union (M α β) where
  union := inst.union

def Mappoid.update {α β M} [inst: Mappoid M] [DecidableEq α] (m: M α β) (k: α) (v: β): M α β
  := inst.union (inst.single k v) m


scoped notation:55 m1:55 " ÷ " m2:56 => Mappoid.remove m1 m2
scoped notation "∅[" k " => " v "]" => Mappoid.single k v
scoped notation m "[" k " => " v "]" => Mappoid.update m k v

example {α β M} [inst: Mappoid M] [DecidableEq α] (m1 m2 m3: M α β):
  m1 ∪ m2 ∪ m3 = (m1 ∪ m2) ∪ m3
:= by
  rfl

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

def Mappoid.disjoint3 {α β M} [Mappoid M] (m1 m2 m3: M α β) :=
  m1 ⊥ m2 ∧ m2 ⊥ m3 ∧ m3 ⊥ m1

scoped notation:51 m1:52 " ⊥ " m2:52 " ⊥ " m3:52 => Mappoid.disjoint3 m1 m2 m3


def Mappoid.agree {α β M} [Mappoid M] (m1 m2: M α β) :=
  ∀ (k: α) (v1 v2: β), m1 k = some v1 → m2 k = some v2 → v1 = v2


scoped notation:50 m1:50 " ↓ " m2:51 => Mappoid.agree m1 m2

@[refl, simp, grind .]
theorem Mappoid.agree.refl {α β M} [Mappoid M] (m: M α β):
  m ↓ m
:= by
  intro k v1 v2 H1 H2
  simp_all


@[symm, grind .]
theorem Mappoid.agree_symm {α β M} [Mappoid M] {m1 m2: M α β}:
  m1 ↓ m2 → m2 ↓ m1
:= by
  unfold Mappoid.agree
  grind


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

@[grind =]
theorem Mappoid.disjoin_eq {α β M} [Mappoid M] {m1 m2: M α β} :
  m1 ⊥ m2 ↔ ∀ (k: α), k ∉ m1 ∨ k ∉ m2
:= by
  simp [Mappoid.disjoint, Membership.mem]

@[grind =]
theorem Mappoid.disjoin_imp {α β M} [Mappoid M] {m1 m2: M α β}:
  m1 ⊥ m2 ↔ (∀ k, k ∈ m1 → ¬ k ∈ m2)
:= by
  simp_all [Mappoid.disjoint, Membership.mem]
  grind

@[symm, grind .]
theorem Mappoid.disjoint_symm {α β M} [Mappoid M] {m1 m2: M α β} :
  m1 ⊥ m2 → m2 ⊥ m1
:= by
  simp [Mappoid.disjoint]
  intro H k
  cases H k
  . right
    assumption
  . left
    assumption


def Mappoid.eq {α β M} [Mappoid M] (m1 m2: M α β) :=
  ∀ (k: α), m1 k = m2 k

scoped notation:50 m1:50 " ≈ " m2:51 => Mappoid.eq m1 m2

@[simp, grind =_]
theorem Mappoid.eq_iff {α β M} [Mappoid M] (m1 m2: M α β) :
  (∀ (k: α), m1 k = m2 k) ↔ m1 ≈ m2
:= by
  simp [Mappoid.eq]


@[refl, grind =]
theorem Mappoid.eq.refl {α β M} [Mappoid M] (m: M α β): m ≈ m := by
  intro k
  simp


@[symm, grind .]
theorem Mappoid.eq.symm {α β M} [Mappoid M] {m1 m2: M α β}:
  m1 ≈ m2 → m2 ≈ m1
:= by
  intro H k
  specialize H k
  simp_all


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
  single k v := fun k' => if k = k' then some v else none
  remove := fun m k k' => if k = k' then none else m k'
  filter := fun p m k =>
    match m k with
    | none => none
    | some v => if p k v then some v else none


@[simp, grind .]
theorem Map.extensionality {α β: Type} {m1 m2: Map α β}:
  m1 ≈ m2 ↔ m1 = m2
:= by
  apply Iff.intro
  . intro H
    funext k
    specialize H k
    simp [Mappoid.find] at H
    exact H
  . intro H
    rw [H]


@[grind =]
theorem Map.disjoint_comm {α β} {m1 m2: Map α β}:
  m1 ⊥ m2 ->
  m1 ∪ m2 = m2 ∪ m1
:= by
  intro H
  funext k
  cases H k <;>
  . simp [Mappoid.union, Mappoid.find, Union.union, *] at *
    repeat split <;> simp_all


instance: DisjointComm Map where
  disjoint_comm := by
    simp
    apply Map.disjoint_comm

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

theorem Map.union_finite {α β: Type} {m1 m2: Map α β}:
  m1.finite → m2.finite → (m1 ∪ m2).finite
:= by
  intro ⟨l1, H1⟩ ⟨l2, H2⟩
  unfold Map.finite
  exists (l1 ++ l2)
  intro k
  simp [Mappoid.union, Union.union]
  grind

theorem Map.single_finite {α β: Type} [DecidableEq α] {k: α} {v: β} :
  (Mappoid.single k v : Map α β).finite
:= by
  simp [Map.finite, Mappoid.single]
  exists [k]
  grind

theorem Map.update_finite {α β: Type} [DecidableEq α] (m: Map α β) (k: α) (v: β) :
  m.finite → (Mappoid.update m k v).finite
:= by
  intro ⟨l, H⟩
  unfold Map.finite
  exists (k :: l)
  intro k'
  simp [Mappoid.update, Mappoid.single, Mappoid.union]
  grind

theorem Map.remove_finite {α β: Type} [DecidableEq α] {m: Map α β} {k: α}:
  Map.finite m → Map.finite (m ÷ k)
:= by
  intro ⟨l, H⟩
  unfold Map.finite
  exists l
  intro k'
  simp [Mappoid.remove]
  grind

theorem Map.filter_finite {α β: Type} {p: α → β → Bool} {m: Map α β} :
  Map.finite m → Map.finite (Mappoid.filter p m)
:= by
  intro ⟨l, H⟩
  unfold Map.finite
  exists l
  intro k
  simp [Mappoid.filter]
  grind


@[simp, grind =]
theorem Map.find_eq {α β: Type} (m: Map α β) (k: α):
  Mappoid.find m k = m k
:= by
  simp [Mappoid.find]


@[simp, grind .]
theorem Map.empty_find {α β: Type} (k: α):
  (∅ : Map α β) k = none
:= by
  simp [Mappoid.empty, EmptyCollection.emptyCollection]


@[simp]
theorem Map.single_elem? {α β} [DecidableEq α] {x: α} {v: β}:
  (∅ [x => v]: Map α β)[x]? = some v
:= by
  simp [EmptyCollection.emptyCollection, Mappoid.empty, Mappoid.update]
  simp [GetElem?.getElem?, Mappoid.find, Mappoid.single, Mappoid.union]


@[simp]
theorem Map.single_elem! {α β} [DecidableEq α] [Inhabited β] {x: α} {v: β}:
  (∅ [x => v]: Map α β)[x]! = v
:= by
  simp [EmptyCollection.emptyCollection, Mappoid.empty, Mappoid.update]
  simp [GetElem?.getElem!, Mappoid.find, Mappoid.single, Mappoid.union]


@[simp, grind =]
theorem Map.read_union_left {α β} [DecidableEq α] [Inhabited β] {m1 m2: Map α β} {x: α}:
  x ∈ m1 →
  (m1 ∪ m2)[x]! = m1[x]!
:= by
  intro H
  simp [Membership.mem, Mappoid.find] at H
  simp [Mappoid.union, Union.union, Mappoid.find, GetElem?.getElem!]
  split
  . split <;> simp_all
  . split <;> simp_all

@[simp, grind =]
theorem Map.read_union_right {α β} [DecidableEq α] [Inhabited β] {m1 m2: Map α β} {x: α}:
  ¬ x ∈ m1 →
  (m1 ∪ m2)[x]! = m2[x]!
:= by
  intro H
  simp [Membership.mem, Mappoid.find] at H
  simp [Mappoid.union, Union.union, Mappoid.find, GetElem?.getElem!]
  split
  . split <;> simp_all
  . split <;> simp_all


@[simp, grind =]
theorem Map.update_single_eq {α β} [DecidableEq α] {k: α} {v: β}:
  ∅[k => v] [k => v] = (∅[k => v] : Map α β)
:= by
  simp [Mappoid.update, Mappoid.union]
  funext
  grind

/-!
## Implementation of `FMap`
-/
def FMap (α β: Type): Type := { m: Map α β // m.finite }

instance: Mappoid FMap where
  find := fun m k => m.val k
  empty := ⟨∅, Map.empty_finite⟩
  union := fun m1 m2 =>
    ⟨m1.val ∪ m2.val, Map.union_finite m1.property m2.property⟩
  single := fun k v =>
    ⟨Mappoid.single k v, Map.single_finite⟩
  remove := fun m k =>
    ⟨m.val ÷ k, Map.remove_finite m.property⟩
  filter := fun p m =>
    ⟨Mappoid.filter p m.val, Map.filter_finite m.property⟩


/-!
### Properties of `FMap`
-/

@[simp, grind =]
theorem FMap.find_eq {α β: Type} (m: FMap α β) (k: α):
  Mappoid.find m k = m.val k
:= by
  simp [Mappoid.find]

@[simp, grind =]
theorem FMap.find_eq_func {α β: Type} (m: FMap α β) (k: α):
  m k = m.val k
:= by
  simp [Mappoid.find]

@[grind =]
theorem FMap.mem_eq {α β: Type} (m: FMap α β) (k: α):
  k ∈ m ↔ k ∈ m.val
:= by
  simp [Membership.mem, Mappoid.find]

theorem FMap.mem_spec {α β: Type} (m: FMap α β):
  ∃ (l: List α), ∀ (k: α), k ∈ m ↔ k ∈ l
:= by
  rcases m with ⟨m, F⟩
  simp [Map.finite] at F
  rcases F with ⟨l, H⟩
  let l' := l.filter (fun k => (m k).isSome)
  exists l'
  simp_all [Membership.mem, Mappoid.find]
  intro k
  apply Iff.intro
  . intro H'
    cases H k <;> try contradiction
    apply List.mem_filter.mpr
    simp_all [Option.isSome]
    split <;> simp_all
  . intro H
    have ⟨_, H⟩ := List.mem_filter.mp H
    unfold Option.isSome at H
    split at H <;> simp_all

@[grind =_]
theorem FMap.eq_iff {α β } (m1 m2: FMap α β) :
  m1 = m2 ↔ m1.val = m2.val
:= by
  apply Subtype.ext_iff


@[simp, grind =]
theorem FMap.extensionality {α β: Type} {m1 m2: FMap α β} :
  m1 ≈ m2 ↔ m1 = m2
:= by
  apply Iff.intro
  . intro H
    apply Subtype.ext_iff.mpr
    apply Map.extensionality.mp
    exact H
  . intro H
    rw [H]

@[simp, grind .]
theorem FMap.congr {α β: Type} {m1 m2: FMap α β} :
  m1 = m2 -> forall k, m1 k = m2 k
:= by
  grind

@[simp, grind =]
theorem FMap.empty_find {α β: Type} (k: α):
  (∅: FMap α β) k = none
:= by
  simp [Mappoid.find]
  apply Map.empty_find

@[simp, grind .]
theorem FMap.empty_find' {α β: Type} (k: α):
  (∅: FMap α β).val k = none
:= by
  apply Map.empty_find

@[simp, grind .]
theorem FMap.single_find_same {α β: Type} [DecidableEq α] {x: α} {v: β}:
  (∅[x => v]: FMap α β) x = v
:= by
  simp [Mappoid.find, Mappoid.single]

@[simp, grind =]
theorem FMap.union_val {α β: Type} {m1 m2: FMap α β} :
  (Mappoid.union m1 m2).val = Mappoid.union m1.val m2.val
:= by
  funext k
  simp [Mappoid.union, Union.union]

@[simp, grind =]
theorem FMap.union_val' {α β: Type} {m1 m2: FMap α β} :
  (m1 ∪ m2).val = m1.val ∪ m2.val
:= by
  funext k
  simp [Mappoid.union, Union.union]

@[simp, grind =]
theorem FMap.single_val {α β: Type} [DecidableEq α] {k: α} {v: β} :
  (∅[k => v]: FMap α β).val = ∅[k => v]
:= by
  simp [Mappoid.single]
  funext
  rfl

@[simp, grind =]
theorem FMap.update_val {α β: Type} [DecidableEq α] {m: FMap α β} {k: α} {v: β} :
  (m[k => v]).val = m.val[k => v]
:= by
  simp [Mappoid.update]

@[grind =]
theorem FMap.disjoint_val {α β: Type} {m1 m2: FMap α β} :
  (m1 ⊥ m2) ↔ (m1.val ⊥ m2.val)
:= by
  simp_all [Mappoid.disjoint, Mappoid.find]

@[simp, grind =]
theorem FMap.remove_val {α β: Type} [DecidableEq α] {m: FMap α β} {k: α} :
  (m ÷ k).val = m.val ÷ k
:= by
  funext k
  simp [Mappoid.remove]

/-!
#### Domain
-/
@[grind .]
theorem FMap.mem_single_eq {α β} [DecidableEq α] {x y: α} {v: β}:
  y ∈ (∅[x => v]: FMap α β) → y = x
:= by
  intro H
  simp [Membership.mem, Mappoid.find, Mappoid.single] at H
  simp_all

@[simp, grind .]
theorem FMap.mem_single {α β} [DecidableEq α] {x: α} {v: β}:
  x ∈ (∅[x => v]: FMap α β)
:= by
  simp [Membership.mem, Mappoid.find, Mappoid.single]

@[grind =]
theorem FMap.mem_union {α β} {m1 m2: FMap α β} {k: α}:
  k ∈ m1 ∪ m2 ↔ k ∈ m1 ∨ k ∈ m2
:= by
  simp [Membership.mem, Mappoid.find, Mappoid.union, Union.union]
  grind

@[grind .]
theorem FMap.mem_union_left {α β} {m1 m2: FMap α β} {k: α}:
  k ∈ m1 → k ∈ m1 ∪ m2
:= by
  grind

@[grind .]
theorem FMap.mem_union_right {α β} {m1 m2: FMap α β} {k: α}:
  k ∈ m2 → k ∈ m1 ∪ m2
:= by
  grind

@[grind .]
theorem FMap.update_eq {α β} [DecidableEq α] {m: FMap α β} {x y: α} {v: β}:
  y ∈ m [x => v] → (x = y ∨ y ∈ m)
:= by
  intro H
  simp [Membership.mem, Mappoid.update, Mappoid.find, Mappoid.single, Mappoid.union, Union.union] at H
  split at H
  . simp_all
  . simp_all [Membership.mem, Mappoid.find]

@[grind .]
theorem FMap.remove_eq {α β} [DecidableEq α] {m: FMap α β} {x y: α}:
  y ∈ m ÷ x → (x ≠ y ∧ y ∈ m)
:= by
  intro H
  simp [Membership.mem, Mappoid.remove, Mappoid.find] at H
  rcases H with ⟨H1, H2⟩
  and_intros
  . simp_all
  . simp_all [Membership.mem, Mappoid.find]

@[grind .]
theorem FMap.disjoint_single_of_not_indom {α β} [DecidableEq α] {m: FMap α β} {x: α} {v: β}:
  x ∉ m → (∅[x => v]: FMap α β) ⊥ m
:= by
  grind

/-!
#### Disjointness
-/
@[simp, grind =]
theorem FMap.disjoint_comm {α β} {m1 m2: FMap α β}:
  m1 ⊥ m2 ->
  m1 ∪ m2 = m2 ∪ m1
:= by
  intro H
  apply Subtype.ext_iff.mpr
  apply Map.disjoint_comm
  grind

@[simp, grind .]
theorem FMap.disjoint_empty_left {α β} (m: FMap α β) :
  ∅ ⊥ m
:= by
  intro k
  left
  simp [Mappoid.find, Mappoid.empty, EmptyCollection.emptyCollection]

@[simp, grind .]
theorem FMap.disjoint_empty_right {α β} (m: FMap α β) :
  m ⊥ ∅
:= by
  symm
  apply FMap.disjoint_empty_left

@[simp, grind =]
theorem FMap.disjoint_union_eq_right {α β} {m1 m2 m3: FMap α β}:
  m1 ⊥ (m2 ∪ m3) ↔ (m1 ⊥ m2 ∧ m1 ⊥ m3)
:= by
  grind

@[simp, grind =]
theorem FMap.disjoint_union_eq_left {α β} {m1 m2 m3: FMap α β}:
  (m1 ∪ m2) ⊥ m3 ↔ (m1 ⊥ m3 ∧ m2 ⊥ m3)
:= by
  grind

@[simp, grind =]
theorem FMap.disjoint_single_single {α β} [DecidableEq α] {x1 x2: α} {v1 v2: β}:
  (∅[x1 => v1]: FMap α β) ⊥ (∅[x2 => v2]: FMap α β) ↔ x1 ≠ x2
:= by
  grind

@[simp, grind .]
theorem FMap.disjoint_single_set {α β} [DecidableEq α] {x: α} {v1 v2: β} {m: FMap α β}:
  (∅[x => v1]: FMap α β) ⊥ m → (∅[x => v2]: FMap α β) ⊥ m
:= by
  grind

@[simp, grind .]
theorem FMap.disjoint_update_left {α β} [DecidableEq α] {m1 m2: FMap α β} {x: α} {v: β}:
  m1 ⊥ m2 →
  x ∈ m1 →
  (m1 [x => v]) ⊥ m2
:= by
  grind

@[simp, grind .]
theorem FMap.disjoint_update_not_right {α β} [DecidableEq α] {m1 m2: FMap α β} {x: α} {v: β}:
  m1 ⊥ m2 →
  (¬ x ∈ m2) →
  m1 [x => v] ⊥ m2
:= by
  grind

@[simp, grind .]
theorem FMap.disjoin_remove_left {α β} [DecidableEq α] {m1 m2: FMap α β} {x: α}:
  m1 ⊥ m2 →
  (m1 ÷ x) ⊥ m2
:= by
  grind

/-!
#### Union
-/
@[simp, grind =]
theorem FMap.union_self {α β} [DecidableEq α] {m: FMap α β}:
  m ∪ m = m
:= by
  apply Subtype.ext_iff.mpr
  funext k
  simp [Mappoid.union, Union.union]
  grind

@[simp, grind =]
theorem FMap.union_empty_left {α β} [DecidableEq α] {m: FMap α β}:
  ∅ ∪ m = m
:= by
  apply Subtype.ext_iff.mpr
  funext k
  simp [Mappoid.union, Union.union, Mappoid.empty, EmptyCollection.emptyCollection]

@[simp, grind =]
theorem FMap.union_empty_right {α β} [DecidableEq α] {m: FMap α β}:
  m ∪ ∅ = m
:= by
  grind

@[grind .]
theorem FMap.union_eq_empty_inv_left {α β} [DecidableEq α] {m1 m2: FMap α β}:
  m1 ∪ m2 = ∅ → m1 = ∅
:= by
  intro H
  apply Subtype.ext_iff.mpr
  replace H := congrArg (fun m => m.val) H
  simp at H
  funext k
  replace H := congrFun H k
  simp_all [Mappoid.empty, Mappoid.union, Union.union, EmptyCollection.emptyCollection]
  split at H <;> simp_all

@[grind .]
theorem FMap.union_eq_empty_inv_right {α β} [DecidableEq α] {m1 m2: FMap α β}:
  m1 ∪ m2 = ∅ → m2 = ∅
:= by
  grind

@[simp, grind =]
theorem FMap.agree_union_comm {α β} [DecidableEq α] {m1 m2: FMap α β}:
  m1 ↓ m2 →
  m1 ∪ m2 = m2 ∪ m1
:= by
  intro H
  simp [Mappoid.agree, Mappoid.find] at H
  apply Subtype.ext_iff.mpr
  funext k
  simp [Mappoid.union, Union.union]
  grind

@[simp, grind =]
theorem FMap.union_assoc {α β} [DecidableEq α] {m1 m2 m3: FMap α β}:
  m1 ∪ (m2 ∪ m3) = (m1 ∪ m2) ∪ m3
:= by
  apply Subtype.ext_iff.mpr
  funext k
  simp [Mappoid.union, Union.union]
  grind

@[grind .]
theorem FMap.union_eq_inv_of_disjoint {α β} [DecidableEq α] {m1 m1' m2: FMap α β}:
  m1 ⊥ m2 →
  m1' ⊥ m2 →
  m1 ∪ m2 = m1' ∪ m2 →
  m1 = m1'
:= by
  intro H1 H2 H3
  apply Subtype.ext_iff.mpr
  replace H3 := congrArg (fun m => m.val) H3
  simp at H3
  funext k
  replace H3 := congrFun H3 k
  simp_all [Mappoid.union, Union.union, Mappoid.find, Mappoid.disjoint]
  grind

/-!
#### Compatibility
-/

@[simp, grind .]
theorem FMap.agree.ofUnion {α β} [DecidableEq α] {m1 m2: FMap α β}:
  m1 ⊥ m2 →
  m1 ↓ m2
:= by
  unfold Mappoid.agree Mappoid.disjoint
  grind

instance {α β} {m1 m2: FMap α β} [DecidableEq α]: Coe (m1 ⊥ m2) (m1 ↓ m2) where
  coe := FMap.agree.ofUnion

@[simp, grind .]
theorem FMap.agree_empty_left {α β} [DecidableEq α] {m: FMap α β}:
  ∅ ↓ m
:= by
  grind

@[simp, grind .]
theorem FMap.agree_empty_right {α β} [DecidableEq α] {m: FMap α β}:
  m ↓ ∅
:= by
  grind

@[simp, grind .]
theorem FMap.agree_union_left {α β} [DecidableEq α] {m1 m2 m3: FMap α β}:
  m1 ↓ m3 →
  m2 ↓ m3 →
  m1 ∪ m2 ↓ m3
:= by
  unfold Mappoid.agree
  simp [Mappoid.union, Union.union]
  grind

@[simp, grind .]
theorem FMap.agree_union_right {α β} [DecidableEq α] {m1 m2 m3: FMap α β}:
  m1 ↓ m2 →
  m1 ↓ m3 →
  m1 ↓ (m2 ∪ m3)
:= by
  grind

@[simp, grind .]
theorem FMap.agree_union_lr {α β} [DecidableEq α] {m1 n1 m2 n2: FMap α β}:
  n1 ↓ n2 →
  (m1 ⊥ m2 ⊥ (n1 ∪ n2)) →
  (m1 ∪ m2) ↓ (n1 ∪ n2)
:= by
  unfold Mappoid.disjoint3
  grind

@[simp, grind .]
theorem FMap.agree_union_ll_inv {α β} [DecidableEq α] {m1 m2 m3: FMap α β}:
  (m1 ∪ m2) ↓ m3 →
  m1 ↓ m3
:= by
  intro H
  simp_all [Mappoid.agree, Mappoid.union, Union.union, Mappoid.find]
  grind

@[simp, grind .]
theorem FMap.agree_union_rl_inv {α β} [DecidableEq α] {m1 m2 m3: FMap α β}:
  m1 ↓ (m2 ∪ m3) →
  m1 ↓ m2
:= by
  grind

theorem FMap.agree_union_lr_inv_agree_agree {α β} [DecidableEq α] {m1 m2 m3: FMap α β}:
  (m1 ∪ m2) ↓ m3 →
  m1 ↓ m2 →
  m1 ↓ m3
:= by
  grind

theorem FMap.agree_union_rr_inv_agree {α β} [DecidableEq α] {m1 m2 m3: FMap α β}:
  m1 ↓ (m2 ∪ m3) →
  m2 ↓ m3 →
  m1 ↓ m3
:= by
  grind

theorem FMap.agree_union_l_inv {α β} [DecidableEq α] {m1 m2 m3: FMap α β}:
  (m1 ∪ m2) ↓ m3 →
  m1 ↓ m2 →
  m1 ↓ m3 ∧ m2 ↓ m3
:= by
  grind

theorem FMap.agree_union_r_inv {α β} [DecidableEq α] {m1 m2 m3: FMap α β}:
  m1 ↓ (m2 ∪ m3) →
  m2 ↓ m3 →
  m1 ↓ m2 ∧ m1 ↓ m3
:= by
  grind


/-!
#### Read
-/
@[simp, grind =]
theorem FMap.elem!_eq {α β} [DecidableEq α] [Inhabited β] {m: FMap α β} {x: α}:
  m[x]! = m.val[x]!
:= by
  simp [GetElem?.getElem!, Mappoid.find]

@[simp, grind =]
theorem FMap.elem?_eq {α β} [DecidableEq α] [Inhabited β] {m: FMap α β} {x: α}:
  m[x]? = m.val[x]?
:= by
  simp [GetElem?.getElem?, Mappoid.find]

@[simp]
theorem FMap.single_elem? {α β} [DecidableEq α] [Inhabited β] {x: α} {v: β}:
  (∅[x => v]: FMap α β)[x]? = some v
:= by
  simp [Mappoid.single]
  simp [GetElem?.getElem?, Mappoid.find]

@[simp]
theorem FMap.read_single {α β} [DecidableEq α] [Inhabited β] {x: α} {v: β}:
  (∅[x => v]: FMap α β)[x]! = v
:= by
  simp [Mappoid.single]
  simp [GetElem?.getElem!, Mappoid.find]

@[simp, grind =]
theorem FMap.read_union_left {α β} [DecidableEq α] [Inhabited β] {m1 m2: FMap α β} {x: α}:
  x ∈ m1 →
  (m1 ∪ m2)[x]! = m1[x]!
:= by
  intro H
  simp
  apply Map.read_union_left
  simp_all [Membership.mem, Mappoid.find]

@[simp, grind =]
theorem FMap.read_union_right {α β} [DecidableEq α] [Inhabited β] {m1 m2: FMap α β} {x: α}:
  ¬ x ∈ m1 →
  (m1 ∪ m2)[x]! = m2[x]!
:= by
  intro H
  simp
  apply Map.read_union_right
  simp_all [Membership.mem, Mappoid.find]

/-!
#### Update
-/
/--
Note that `∅ [k => v]` is different from `∅[k => v]`. The former is `Mappoid.update` while
the latter is `Mappoid.single`. The theorem states that they are equal.
-/
@[simp, grind =]
theorem FMap.update_empty {α β} [DecidableEq α] {k: α} {v: β}:
  (∅ [k => v] : FMap α β) = (∅[k => v] : FMap α β)
:= by
  simp [Mappoid.update, EmptyCollection.emptyCollection]
  simp [Mappoid.union, Union.union, Mappoid.empty, Mappoid.single]
  grind

theorem FMap.union_single_eq {α β} [DecidableEq α] {m: FMap α β} {k: α} {v: β}:
  (∅[k => v] ∪ m : FMap α β) = m[k => v]
:= by
  simp [Mappoid.update, Union.union]

@[simp, grind =]
theorem FMap.update_single_eq {α β} [DecidableEq α] {k: α} {v: β}:
  ∅[k => v] [k => v] = (∅[k => v] : FMap α β)
:= by
  simp [FMap.eq_iff]


@[simp, grind =]
theorem FMap.update_union_left {α β} [DecidableEq α] {m1 m2: FMap α β} {k: α} {v: β}:
  k ∈ m1 →
  (m1 ∪ m2)[k => v] = m1[k => v] ∪ m2
:= by
  intro H
  simp [Mappoid.update, Union.union, Mappoid.union]
  grind


@[simp, grind =]
theorem FMap.update_union_right {α β} [DecidableEq α] {m1 m2: FMap α β} {k: α} {v: β}:
  ¬ k ∈ m1 →
  (m1 ∪ m2)[k => v] = m1 ∪ m2[k => v]
:= by
  intro H
  apply Subtype.ext_iff.mpr
  funext k'
  simp_all [Mappoid.update, Union.union, Mappoid.union, Mappoid.single, Membership.mem, Mappoid.find]
  grind

@[simp, grind =]
theorem FMap.update_union_not_left {α β} [DecidableEq α] {m1 m2: FMap α β} {k: α} {v: β}:
  ¬ k ∈ m1 →
  (m1 ∪ m2)[k => v] = m1 ∪ m2[k => v]
:= by
  grind

@[simp, grind =]
theorem FMap.update_union_not_right {α β} [DecidableEq α] {m1 m2: FMap α β} {k: α} {v: β}:
  ¬ k ∈ m2 →
  (m1 ∪ m2)[k => v] = m1[k => v] ∪ m2
:= by
  intro H
  apply Subtype.ext_iff.mpr
  funext k'
  simp_all [Mappoid.update, Union.union, Mappoid.union, Mappoid.single, Membership.mem, Mappoid.find]
  grind

/-!
#### Removal
-/
@[simp, grind =]
theorem FMap.remove_empty {α β} [DecidableEq α] {k: α}:
  (∅ ÷ k : FMap α β) = ∅
:= by
  simp [Mappoid.remove, EmptyCollection.emptyCollection, Mappoid.empty]
  grind

@[simp, grind =]
theorem FMap.remove_single {α β} [DecidableEq α] {k: α} {v}:
  (∅[k => v] ÷ k : FMap α β) = ∅
:= by
  simp [Mappoid.remove, EmptyCollection.emptyCollection, Mappoid.empty, Mappoid.single]
  grind

@[simp, grind =]
theorem FMap.remove_disjoint_left {α β} [DecidableEq α] {m1 m2: FMap α β} {k: α}:
  k ∈ m1 →
  m1 ⊥ m2 →
  (m1 ∪ m2) ÷ k = (m1 ÷ k) ∪ m2
:= by
  intro H1 H2
  simp [FMap.mem_eq] at H1
  apply Subtype.ext_iff.mpr
  simp_all
  simp [Membership.mem] at H1
  simp [Mappoid.disjoint] at H2
  funext k'
  specialize H2 k'
  simp [Mappoid.remove, Mappoid.union, Union.union]
  split
  . split <;> simp_all
  . split <;> grind

@[simp, grind =]
theorem FMap.remove_union_single_left {α β} [DecidableEq α] {m: FMap α β} {k: α} {v: β}:
  ¬ k ∈ m →
  (∅[k => v] ∪ m) ÷ k = m
:= by
  grind

@[simp, grind =]
theorem FMap.remove_update_left {α β} [DecidableEq α] {m: FMap α β} {k: α} {v: β}:
  ¬ k ∈ m →
  (m[k => v]) ÷ k = m
:= by
  exact FMap.remove_union_single_left

/-!
#### Tactics
-/
macro "fmap_simp" : tactic => `(tactic|
  (try unfold Mappoid.disjoint3 at *) <;> try simp_all [
  FMap.union_assoc, FMap.union_empty_left, FMap.union_empty_right,
  FMap.union_self,
  FMap.disjoint_union_eq_left, FMap.disjoint_union_eq_right,
  FMap.disjoint_empty_left, FMap.disjoint_empty_right,
  FMap.disjoint_comm, FMap.agree_union_lr,
  FMap.agree_union_ll_inv, FMap.agree_union_rl_inv, FMap.agree_union_rr_inv_agree,
  FMap.agree_union_l_inv, FMap.agree_union_r_inv

])

macro "fmap_eq": tactic => `(tactic|
  fmap_simp <;>
  intros <;>
  apply Subtype.ext_iff.mpr <;>
  funext <;>
  grind
)

macro "fmap" : tactic => `(tactic| fmap_simp <;> (try grind) <;> fmap_eq)

theorem FMap.union_eq_cancel_1 {α β} [DecidableEq α] {m1 m2 m2': FMap α β}:
  m2 = m2' →
  m1 ∪ m2 = m1 ∪ m2'
:= by
  fmap

theorem FMap.union_eq_cancel_2 {α β} [DecidableEq α] {m1 m1' m2 m2': FMap α β}:
  m1 ⊥ m1' →
  m2 = m1' ∪ m2' →
  m1 ∪ m2 = m1' ∪ m1 ∪ m2'
:= by
  fmap


theorem FMap.union_eq_cancel_3 {α β} [DecidableEq α] {m1 m1' m2 m2' m3': FMap α β}:
  m1 ⊥ (m1' ∪ m2') →
  m2 = m1' ∪ (m2' ∪ m3') →
  m1 ∪ m2 = m1' ∪ m2' ∪ m1 ∪ m3'
:= by
  fmap

theorem FMap.fmap_eq_demo {α β} [DecidableEq α] {m1 m2 m3 m4 m5: FMap α β}:
  m1 ⊥ m2 ⊥ m3 →
  (m1 ∪ m2 ∪ m3) ⊥ m4 ⊥ m5 →
  m1 = m2 ∪ m3 →
  m4 ∪ m1 ∪ m5 = m2 ∪ m5 ∪ m4 ∪ m3
:= by
  fmap

/-!
### Existence of Fresh Locations
#### New location in a list
-/

def FMap.newLoc (l: List Nat): Nat := 1 + l.foldr (· + ·) 0

theorem FMap.newLoc_le {l: List Nat} {n: Nat}:
  n ∈ l → n < FMap.newLoc l
:= by
  intro H
  induction l generalizing n
    <;> simp_all [FMap.newLoc, List.foldr]
    <;> grind

theorem FMap.newLoc_ge (l: List Nat):
  ∃ n, ∀ i, (n + i) ∉ l
:= by
  exists FMap.newLoc l
  intro i contra
  replace contra := FMap.newLoc_le contra
  omega

theorem FMap.exists_refresh_ge {β} {null} {m: FMap Nat β}:
  ∃ n, (∀ i, n + i ∉ m) ∧ n ≠ null
:= by
  have ⟨l, H⟩ := m.mem_spec
  rcases FMap.newLoc_ge (null :: l) with ⟨n, H1⟩
  exists n
  grind [H1 0]

theorem FMap.newLoc_not_mem (l: List Nat):
  ∃ n, n ∉ l
:= by
  rcases FMap.newLoc_ge l with ⟨n, H⟩
  exists n
  exact H 0

theorem FMap.exists_refresh {β} {null} {m: FMap Nat β}:
  ∃ n, n ∉ m ∧ n ≠ null
:= by
  have ⟨n, H1, H2⟩ := m.exists_refresh_ge (null := null)
  exists n
  grind [H1 0]

theorem FMap.single_refresh {β} {null} {m: FMap Nat β} {v}:
  ∃ x: Nat, ∅[x => v] ⊥ m ∧ x ≠ null
:= by
  have ⟨x, H1, H2⟩ := m.exists_refresh (null := null)
  exists x
  grind

/-!
#### Consecutive locations in a `FMap`
-/
@[simp, grind =]
def FMap.conseq {β} (vs: List β) (start: Nat): FMap Nat β :=
  match vs with
  | [] => ∅
  | v :: vs' => (∅[start => v]) ∪ FMap.conseq vs' (start + 1)

@[simp, grind =]
theorem FMap.conseq_elem_spec {β} {vs: List β} {start: Nat} {k: Nat}:
  k ∈ FMap.conseq vs start ↔ (start ≤ k ∧ k < start + vs.length)
:= by
  induction vs generalizing start
  case nil =>
    simp [FMap.conseq, Membership.mem, Mappoid.find, Mappoid.empty, EmptyCollection.emptyCollection]
  case cons v vs' IH =>
    simp
    grind

theorem FMap.conseq_refresh {β} {null} {m: FMap Nat β} {vs: List β}:
  ∃ x: Nat, FMap.conseq vs x ⊥ m ∧ x ≠ null
:= by
  have ⟨x, H1, H2⟩ := m.exists_refresh_ge (null := null)
  exists x
  simp_all
  symm
  apply Mappoid.disjoin_imp.mpr
  intro k H contra
  simp_all
  -- Now that we have `x ≤ k` in `contra`, we have `k = x + (k - x)`.
  -- But `H1` tells us that `x + i ∉ m` for any `i`, which contradicts `H`.
  have _: x + (k - x) ∈ m := by grind
  specialize H1 (k - x)
  contradiction

theorem FMap.disjoint_single_conseq {β} {x y: Nat} {v} {vs: List β}:
  x < y ∨ x ≥ y + vs.length →
  ∅[x => v] ⊥ FMap.conseq vs y
:= by
  grind

def FMap.fresh {β} (null: Nat) (m: FMap Nat β) (x: Nat): Prop :=
  x ∉ m ∧ x ≠ null

instance FMap.fresh_decidable {β} {null: Nat} {m: FMap Nat β} {x: Nat}:
  Decidable (FMap.fresh null m x)
:= by
  unfold FMap.fresh
  cases E: m x
  case some _ =>
    apply Decidable.isFalse
    simp only [Membership.mem]
    simp_all
  case none =>
    simp_all [Membership.mem]
    cases E': x == null
    case true =>
      simp_all
      apply isFalse
      simp
    case false =>
      simp_all
      apply isTrue
      trivial

def FMap.smallest_fresh {β} (null: Nat) (m: FMap Nat β) (x: Nat): Prop :=
  FMap.fresh null m x ∧ ∀ y, y < x → ¬ FMap.fresh null m y

theorem Nat.well_ordered {P: Nat → Prop} [inst: ∀ n, Decidable (P n)]:
  (∃ n, P n) →
  ∃ m, P m ∧ ∀ k, k < m → ¬ P k
:= by
  rintro ⟨n, hn⟩
  let l := List.range (n + 1)
  let h := l.find? (fun k => P k)  -- since P is decidable.
  have _: h ≠ none := by
    intro h
    replace h := List.find?_range_eq_none.mp h
    specialize h n
    simp at h
    contradiction
  have ⟨m, hm⟩: exists m, h = some m := by
    cases E: h with
    | none => contradiction
    | some m => exists m
  replace hm := List.find?_range_eq_some.mp hm
  simp at hm
  rcases hm with ⟨_, _, _⟩
  exists m

theorem FMap.smallest_fresh_exists {β} {null} {m: FMap Nat β}:
  ∃ x, FMap.smallest_fresh null m x
:= by
  unfold FMap.smallest_fresh
  apply Nat.well_ordered
  rcases m.exists_refresh (null := null) with ⟨x, H1, H2⟩
  exists x

@[simp]
theorem FMap.exists_nonempty {β} [Inhabited β]:
  ∃ m, m ≠ (∅: FMap Nat β)
:= by
  exists ∅[0 => default]
  intro H
  replace H := FMap.congr H 0
  simp at H
  simp [Mappoid.single] at H
