import SLF.Semantics
import SLF.Heap

namespace SLF
open Lang Heap

section Triple

@[grind]
def Triple (t: Term) (H: HProp) (Q: Val → HProp) : Prop :=
  ∀ s, H s → Eval s t Q

notation "funloc" p "=>" H => (fun (r: Val) => \∃ p, \[r = Val.loc p] ** H)

end Triple

section Soundness

@[grind]
inductive Terminates : Heap → Term → Prop where
  | step {s t}:
      (∀ {s' t'}, Step s t s' t' → Terminates s' t') →
      Terminates s t

@[grind]
def Safe (s: Heap) (t: Term) : Prop :=
  ∀ s' t', MStep s t s' t' → NonStuck s' t'

@[grind]
def Correct (s: Heap) (t: Term) (Q: Val → HProp) : Prop :=
  ∀ s' (v: Val), MStep s t s' v → Q v s'

inductive SEval : Heap → Term → (Val → HProp) → Prop where
  | val {s v Q}:
      Q v s →
      SEval s (.val v) Q
  | step {s t Q}:
      Reduciable s t →
      (∀ {s' t'}, Step s t s' t' → SEval s' t' Q) →
      SEval s t Q

theorem SEval.terminates {s t Q}:
  SEval s t Q → Terminates s t
:= by
  intro H
  induction H
  case val s v Q HQ =>
    apply Terminates.step
    intro s' t' S
    cases S
  case step s t Q R H IH =>
    apply Terminates.step
    intro s' t' S
    apply IH
    exact S

theorem SEval.safe {s t Q}:
  SEval s t Q → Safe s t
:= by
  intro H
  induction H
  case val s v Q HQ =>
    intro s' t' MS
    cases MS
    case refl =>
      simp
    case step s' t' S _ =>
      cases S
  case step s t Q R _ IH =>
    intro s' t' MS
    cases MS
    case refl =>
      right
      obtain ⟨s'', t'', S⟩ := R
      apply S.reduciable
    case step s'' t'' S MS =>
      specialize IH S
      simp [Safe] at IH
      apply IH
      exact MS

theorem SEval.correct {s t Q}:
  SEval s t Q → Correct s t Q
:= by
  intro H
  induction H
  case val s v Q HQ =>
    simp [Correct]
    intro s' v' MS
    cases MS <;> try contradiction
    exact HQ
  case step s t Q R H IH =>
    intro s' v' MS
    cases MS
    case refl =>
      simp at R
    case step s'' t'' S MS =>
      specialize IH S
      simp [Correct] at IH
      apply IH
      exact MS

theorem SEval.fun {s x t1 Q}:
  Q (Val.fun x t1) s →
  SEval s (.fun x t1) Q
:= by
  grind [SEval]

theorem SEval.fix {s f x t1 Q}:
  Q (Val.fix f x t1) s →
  SEval s (.fix f x t1) Q
:= by
  grind [SEval]

theorem SEval.app_fun {s x v1 v2 t1 Q}:
  v1 = Val.fun x t1 →
  SEval s (Term.subst x v2 t1) Q →
  SEval s (Term.app v1 v2) Q
:= by
  intro H HS
  apply SEval.step
  . grind
  . grind

theorem SEval.app_fix {s f x v1 v2 t1 Q}:
  v1 = Val.fix f x t1 →
  SEval s ((t1.subst f v1).subst x v2) Q →
  SEval s (Term.app v1 v2) Q
:= by
  intro H S
  apply SEval.step
  . grind
  . grind

theorem SEval.seq {s t1 t2 Q1 Q}:
  SEval s t1 Q1 →
  (∀ s1 v1, Q1 v1 s1 → SEval s1 t2 Q) →
  SEval s (Term.seq t1 t2) Q
:= by
  intro HS H
  induction HS -- <;> grind [SEval]
  case val s v Q1 HS =>
    apply SEval.step
    . simp
    . intro s' t' S
      cases S <;> try contradiction
      apply H s v
      exact HS
  case step s t1 Q1 R _ IH =>
    apply SEval.step
    . grind
    . intro s' t' S
      cases S <;> try simp at R
      case seq_ctx t1' S =>
        apply IH
        . exact S
        . exact H

theorem SEval.let {s x t1 t2 Q1 Q}:
  SEval s t1 Q1 →
  (∀ s1 v1, Q1 v1 s1 → SEval s1 (t2.subst x v1) Q) →
  SEval s (Term.let x t1 t2) Q
:= by
  intro HS H
  induction HS -- <;> grind [SEval]
  case val s v Q1 HS =>
    apply SEval.step
    . grind
    . intro s' t' S
      cases S <;> try contradiction
      apply H s v
      exact HS
  case step s t1 Q1 R _ IH =>
    apply SEval.step
    . grind
    . intro s' t' S
      cases S <;> try simp at R
      case let_ctx t1' S =>
        apply IH
        . exact S
        . exact H

theorem SEval.app1 {s1 t1 t2 Q1 Q}:
  SEval s1 t1 Q1 →
  (∀ v1 s2, Q1 v1 s2 → SEval s2 (Term.app v1 t2) Q) →
  SEval s1 (Term.app t1 t2) Q
:= by
  intro HS H
  induction HS
  case val s1 v1 Q1 HS =>
    apply H v1 s1
    exact HS
  case step s1 t1 Q1 R _S IH =>
    apply SEval.step
    . grind
    . intro s' t' S
      cases S <;> grind only [=Reduciable.eq_1]

theorem SEval.app2 {v1: Val}{t2 Q1 s1 Q}:
  SEval s1 t2 Q1 →
  (∀ v2 s2, Q1 v2 s2 → SEval s2 (Term.app v1 v2) Q) →
  SEval s1 (Term.app v1 t2) Q
:= by
  intro HS H
  induction HS
  case val s1 v1 Q1 HS =>
    apply H v1 s1
    exact HS
  case step s1 t1 Q1 R _S IH =>
    apply SEval.step
    . grind
    . intro s' t' S
      cases S <;> grind

theorem SEval.if {s} {b: Bool} {t1 t2 Q}:
  SEval s (if b then t1 else t2) Q →
  SEval s (Term.if b t1 t2) Q
:= by
  intro HS
  apply SEval.step <;> grind

theorem Eval.toSEval {s t Q}:
  Eval s t Q →
  SEval s t Q
:= by
  intro M
  induction M
  case val | «fun» | fix | app_fun | app_fix | «if» =>
    solve_by_elim [
      SEval.val, SEval.fun, SEval.fix,
      SEval.app_fun, SEval.app_fix,
      SEval.seq, SEval.let, SEval.if
    ]
  case unop op s v p q E P =>
    cases E <;> apply SEval.step <;> grind [SEval.val]
  case binop op s v1 v2 p q E P =>
    cases E <;> apply SEval.step <;> grind [SEval.val]
  -- the rest are operators
  case ref s v Q H =>
    apply SEval.step <;> grind [SEval.val]
  case get =>
    apply SEval.step <;> grind [SEval.val]
  case set =>
    apply SEval.step <;> grind [SEval.val]
  case free =>
    apply SEval.step <;> grind [SEval.val]
  all_goals
    grind [
      SEval.val, SEval.fun, SEval.fix,
      SEval.app1, SEval.app2, SEval.app_fun, SEval.app_fix,
      SEval.seq, SEval.let, SEval.if
    ]

theorem Triple.sound {t H Q}:
  Triple t H Q →
  ∀ s, H s → Terminates s t ∧ Safe s t ∧ Correct s t Q
:= by
  intro M s Hs
  specialize M s Hs
  replace M := M.toSEval
  and_intros
  . exact M.terminates
  . exact M.safe
  . exact M.correct

end Soundness
