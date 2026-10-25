import SLF.Triple

namespace SLF

open Lang Map Heap

@[grind]
def WP (t:Term) (Q: Val → HProp) : HProp := fun s => Eval s t Q

@[grind =]
theorem WP.equiv {t H Q}:
  (H ==> WP t Q) ↔ (Triple t H Q)
:= by
  grind

@[simp, grind .]
theorem WP.pre {t Q}:
  Triple t (WP t Q) Q
:= by
  grind

section WPCharacteristic

/--
The weakest precondition is unique up to logical equivalence.
Note, this is an application of Yoneda-lemma.
Since `==>` forms a partial order, i.e. `HProp` is a poset category,
we can think of the two conditions as the equivalence between `Hom[-, wp1 t Q]`
and `Hom[-, wp2 t Q]`. Thus, `wp1` = `wp2`.
-/
theorem WP_unique (wp1 wp2: Term → (Val → HProp) → HProp):
  (∀ t H Q, (Triple t H Q) ↔ (H ==> wp1 t Q)) →
  (∀ t H Q, (Triple t H Q) ↔ (H ==> wp2 t Q)) →
  wp1 = wp2
:= by
  intro E1 E2
  funext t Q
  apply HProp.yoneda_embedding
  intro H
  rewrite [←E1]
  rewrite [←E2]
  rfl

/--
The following two says that `wp` is the weakest precondition for `t` and `Q`:
- `∀ t Q, Triple t (wp t Q) Q`
- `∀ t H Q, Triple t H Q → H ==> wp t Q`

Then, `wp` being the weakest precondition is characterized by the equivalence
`∀ t H Q, H ==> wp t Q ↔ Triple t H Q`.

Note that, the _weakest precondition_ is nothing special but the **colimit** of
all `H: HProp` such that `Triple t H Q` holds. The `Triple t · Q` is a sieve due
to `Triple.conseq`, which is essentially the transitivity of `==>`. Thus this
theorem states nothing but _the colimit is the principal sieve itself_.
-/
theorem WP_characteristic (wp: Term → (Val → HProp) → HProp):
  (
    (∀ t Q, Triple t (wp t Q) Q)
    ∧
    (∀ t H Q, Triple t H Q → H ==> wp t Q)
  )
  ↔
  (∀ t H Q, H ==> wp t Q ↔ Triple t H Q)
:= by
  suffices
    ∀ t Q,
      Triple t (wp t Q) Q ∧ (∀ H, Triple t H Q → H ==> wp t Q)
      ↔ (∀ H, H ==> wp t Q ↔ Triple t H Q)
  by
    grind
  intro t Q
  apply HProp.principal_sieve_colimit (S := fun H => Triple t H Q)
  intro H H' I HT
  apply Triple.conseq
  . exact I
  . rfl
  . exact HT

/--
The weak precondition can also be define only with `HProp` operations and `Triple`,
which does not rely on the explicit definition of `Eval`. Sometimes, `WP` is more
than `Eval`. This shows how to define the weakest precondition from `Triple` and
`HProp` operations.
-/
def WP' (t: Term) (Q: Val → HProp) : HProp :=
  \∃ (H: HProp), H ** \[Triple t H Q]

theorem WP'.equiv {t H Q}:
  H ==> WP' t Q ↔ (Triple t H Q)
:= by
  apply Iff.intro
  . unfold WP'
    intro K
    intro h Hh
    specialize K h Hh
    simp at K
    grind
  . unfold WP'
    intro K
    grind

end WPCharacteristic

section StructruralRules

@[grind .]
theorem WP.conseq {t Q1 Q2}:
  Q1 ===> Q2 →
  WP t Q1 ==> WP t Q2
:= by
  grind

@[grind .]
theorem WP.frame {t H Q}:
  (WP t Q) ** H ==> WP t (Q *+ H)
:= by
  intro h HWP
  unfold WP at *
  obtain ⟨h1, h2, HWP1, Hh2, Hdisj, E⟩ := HWP
  subst h
  apply HWP1.frame_conseq
  . exact Hdisj
  . exact Hh2

@[grind .]
theorem WP.frame_trans {t H1 Q H}:
  H1 ==> WP t Q →
  (H1 ** H) ==> WP t (Q *+ H)
:= by
  open XSimp in
  intro M
  xchange M
  xchange WP.frame
  rfl

@[grind .]
theorem WP.ramified {t Q1 Q2}:
  (WP t Q1) ** (Q1 -** Q2) ==> (WP t Q2)
:= by
  grind

@[grind .]
theorem WP.conseq_frame {t H Q1 Q2}:
  Q1 *+ H ===> Q2 →
  (WP t Q1) ** H ==> (WP t Q2)
:= by
  open XSimp in
  intro M
  rw [←HProp.qwand_eq] at M
  xchange M
  apply WP.ramified

@[grind .]
theorem WP.ramified_trans {t H Q1 Q2}:
  H ==> (WP t Q1) ** (Q1 -** Q2) →
  H ==> (WP t Q2)
:= by
  open XSimp in
  intro M
  xchange M
  apply WP.ramified

end StructruralRules

section ReasoningRules

@[grind .]
theorem WP.eval_like {t1 t2 Q}:
  t1.eval_like t2 →
  WP t1 Q ==> WP t2 Q
:= by
  grind

@[grind .]
theorem WP.val {v Q}:
  Q v ==> WP (.val v) Q
:= by
  grind

@[grind .]
theorem WP.fun {x t Q}:
  Q (.fun x t) ==> WP (.fun x t) Q
:= by
  grind

@[grind .]
theorem WP.fix {f x t Q}:
  Q (.fix f x t) ==> WP (.fix f x t) Q
:= by
  grind

@[grind .]
theorem WP.app_fun {x v1 v2 t1 Q}:
  v1 = Val.fun x t1 →
  WP (t1.subst x v2) Q ==> WP (.app v1 v2) Q
:= by
  grind

@[grind .]
theorem WP.app_fix {f x v1 v2 t1 Q}:
  v1 = Val.fix f x t1 →
  WP ((t1.subst f v1).subst x v2) Q ==> WP (.app v1 v2) Q
:= by
  grind

@[grind .]
theorem WP.seq {t1 t2 Q}:
  WP t1 (fun _ => WP t2 Q) ==> WP (.seq t1 t2) Q
:= by
  grind

@[grind .]
theorem WP.let {x t1 t2 Q}:
  WP t1 (fun v => WP (t2.subst x v) Q) ==> WP (.let x t1 t2) Q
:= by
  unfold WP
  intro h K
  apply Eval.let
  . apply K
  . intro _ _
    apply id

@[grind .]
theorem WP.if {b: Bool} {t1 t2 Q}:
  WP (if b then t1 else t2) Q ==> WP (.if b t1 t2) Q
:= by
  grind

@[grind .]
theorem WP.if_case {b: Bool} {t1 t2 Q}:
  (if b then WP t1 Q else WP t2 Q) ==> WP (.if b t1 t2) Q
:= by
  grind

end ReasoningRules
