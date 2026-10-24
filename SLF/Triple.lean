import SLF.Semantics
import SLF.Heap

namespace SLF
open Map Lang Heap

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

section StructuralRules

@[grind .]
theorem Triple.conseq {t H' Q' H Q}:
  H ==> H' →
  Q' ===> Q →
  Triple t H' Q' →
  Triple t H Q
:= by
  intro HH HQ M
  intro s Hs
  solve_by_elim [Eval.conseq]

@[grind .]
theorem Triple.frame {t H Q H'}:
  Triple t H Q →
  Triple t (H ** H') (Q *+ H')
:= by
  intro M
  rintro h ⟨h1, h2, Hh1, H'h2, Hdisj, E⟩
  specialize M h1 Hh1
  replace M := Eval.frame M Hdisj
  subst h
  apply M.conseq
  intro v
  simp
  apply HProp.imp_frame_right
  intro h H
  subst_eqs
  exact H'h2

@[grind .]
theorem Triple.pure {t} {P:Prop} {H Q}:
  (P → Triple t H Q) →
  Triple t (\[P] ** H) Q
:= by
  intro HT
  simp [Triple]
  intro s HP Hs
  specialize HT HP
  apply HT
  exact Hs

@[simp, grind .]
theorem Triple.pure' {t} {P:Prop} {Q}:
  (P → Triple t \[] Q) →
  Triple t \[P] Q
:= by
  grind

@[grind .]
theorem Triple.exists {t} {α} {J:α → HProp} {Q}:
  (∀ x, Triple t (J x) Q) →
  Triple t (\∃[J]) Q
:= by
  grind

theorem Triple.forall {t} {α} {x: α} {J:α → HProp} {Q}:
  Triple t (J x) Q →
  Triple t (\∀[J]) Q
:= by
  grind

@[grind .]
theorem Triple.wand_pure_left {t P H Q}:
  P →
  Triple t H Q →
  Triple t (\[P] -* H) Q
:= by
  grind

/--
Note that `Triple t (· = h) Q` means `Eval h t Q` exactly.
Thus, to prove `Triple t H Q`, we only have to verify that
`H h` implies `Triple t (· = h) Q` for all `h`.
This turns `Triple t H Q` to triples `Triple t (· = h) Q` for each heap `h`
that satisfy `H`.
-/
@[grind .]
theorem Triple.named_heap {t H Q}:
  (∀ h, H h → Triple t (· = h) Q) →
  Triple t H Q
:= by
  intro K
  simp [Triple] at K
  unfold Triple
  exact K

@[grind .]
theorem Triple.conseq_frame {H2 H1 Q1 t H Q}:
  H ==> H1 ** H2 →
  Q1 *+ H2 ===> Q →
  Triple t H1 Q1 →
  Triple t H Q
:= by
  intro I1 I2 HT
  apply Triple.conseq I1 I2
  apply Triple.frame
  exact HT

@[grind .]
theorem Triple.ramified_frame {H1 Q1 t H Q}:
  H ==> H1 ** (Q1 -** Q) →
  Triple t H1 Q1 →
  Triple t H Q
:= by
  intro I HT
  apply HT.conseq_frame I _
  grind

end StructuralRules

section TermRules

@[grind .]
theorem Triple.eval_like {t1 t2: Term} {H Q}:
  t1.eval_like t2 →
  Triple t1 H Q →
  Triple t2 H Q
:= by
  grind

@[grind .]
theorem Triple.val {v H Q}:
  H ==> Q v →
  Triple (.val v) H Q
:= by
  grind

@[grind .]
theorem Triple.val_minimal {v}:
  Triple (.val v) \[] (fun r => \[r = v])
:= by
  apply Triple.val
  simp

@[grind .]
theorem Triple.fun {x t1 H Q}:
  H ==> Q (.fun x t1) →
  Triple (.fun x t1) H Q
:= by
  grind

@[grind .]
theorem Triple.fix {f x t1 H Q}:
  H ==> Q (.fix f x t1) →
  Triple (.fix f x t1) H Q
:= by
  grind

@[grind .]
theorem Triple.seq {t1 t2 H Q H1}:
  Triple t1 H (fun _ => H1) →
  Triple t2 H1 Q →
  Triple (.seq t1 t2) H Q
:= by
  grind

@[grind .]
theorem Triple.let {x t1 t2 Q1 H Q}:
  Triple t1 H Q1 →
  (∀ v1, Triple (t2.subst x v1) (Q1 v1) Q) →
  Triple (.let x t1 t2) H Q
:= by
  grind

@[grind .]
theorem Triple.let_val {x v1 t2 H Q}:
  Triple (t2.subst x v1) H Q →
  Triple (.let x (.val v1) t2) H Q
:= by
  intro M
  apply Triple.let (Q1 := (fun v => \[v = v1] ** H))
  . intro h Hh
    constructor
    simp
    exact Hh
  . intro v' h Hh
    simp at Hh
    obtain ⟨_, _⟩ := Hh
    subst v'
    apply M
    assumption

@[grind .]
theorem Triple.if {b: Bool} {t1 t2 H Q}:
  Triple (if b then t1 else t2) H Q →
  Triple (Term.if b t1 t2) H Q
:= by
  grind

@[grind .]
theorem Triple.app_fun {x v1 v2 t1 H Q}:
  v1 = Val.fun x t1 →
  Triple (t1.subst x v2) H Q →
  Triple (Term.app v1 v2) H Q
:= by
  grind

@[grind .]
theorem Triple.app_fun_direct {x} {v2: Val} {t1 H Q}:
  Triple (t1.subst x v2) H Q →
  Triple (Term.app (Val.fun x t1) v2) H Q
:= by
  grind

@[grind .]
theorem Triple.app_fix {f x v1 v2 t1 H Q}:
  v1 = Val.fix f x t1 →
  Triple ((t1.subst f v1).subst x v2) H Q →
  Triple (Term.app v1 v2) H Q
:= by
  grind

@[grind .]
theorem Triple.app_fix_direct {f x} {v2: Val} {t1 H Q}:
  Triple ((t1.subst f (Val.fix f x t1)).subst x v2) H Q →
  Triple (Term.app (Val.fix f x t1) v2) H Q
:= by
  grind

end TermRules

section HeapManipulationRules

@[grind .]
theorem Triple.ref {v: Val}:
  Triple [slf| ref [v]]
    \[]
    (fun r => \∃ p: Loc, \[r = p] ** p ~~> v)
:= by
  intro h H
  simp at H; subst h
  apply Eval.ref
  intro p _
  simp

@[grind .]
theorem Triple.get {v: Val} {p: Loc}:
  Triple [slf| ! [p]]
    (p ~~> v)
    (fun r => \[r = v] ** (p ~~> v))
:= by
  intro h H
  simp at H; subst h
  apply Eval.get
  . simp
  . simp
    apply Heap.read_single

@[grind .]
theorem Triple.set {w} {p: Loc} {v: Val}:
  Triple [slf| [p] := [v]]
    (p ~~> w)
    (fun r => \[r = .unit] ** (p ~~> v))
:= by
  intro h H
  simp at H; subst h
  apply Eval.set
  . simp
  . simp

@[grind .]
theorem Triple.free' {p: Loc} {v: Val}:
  Triple [slf| free [p]]
    (p ~~> v)
    (fun r => \[r = .unit])
:= by
  grind

@[grind .]
theorem Triple.free {p: Loc} {v: Val}:
  Triple [slf| free [p]]
    (p ~~> v)
    (fun _ => \[])
:= by
  grind

end HeapManipulationRules

section PrimitiveOpRules

@[grind .]
theorem Triple.unop {op} {v1} {P: Val → Prop}:
  EvalUnOp op v1 P →
  Triple [slf| [op] [v1]] \[] (fun r => \[P r])
:= by
  grind

@[grind .]
theorem Triple.binop {op} {v1 v2} {P: Val → Prop}:
  EvalBinOp op v1 v2 P →
  Triple [slf| [op] [v1] [v2]] \[] (fun r => \[P r])
:= by
  grind

section UnOp

@[grind .]
theorem Triple.rand {n: Int}:
  n > 0 →
  Triple [slf| rand [n]]
    \[]
    (fun r => \[∃ n1: Int, r = n1 ∧ 0 ≤ n1 ∧ n1 < n])
:= by
  grind

@[grind .]
theorem Triple.neg {b1: Bool}:
  Triple [slf| not [b1]]
    \[]
    (fun r => \[r = ! b1])
:= by
  apply Triple.unop
  apply EvalUnOp.neg

@[grind .]
theorem Triple.opp {n1: Int}:
  Triple [slf| - [n1]]
    \[]
    (fun r => \[r = (-n1: Int)])
:= by
  grind [EvalUnOp.opp]

end UnOp

section Arithmetic

@[grind .]
theorem Triple.add {n1 n2: Int}:
  Triple [slf| [n1] + [n2]]
    \[]
    (fun r => \[r = (n1 + n2)])
:= by
  grind

@[grind .]
theorem Triple.sub {n1 n2: Int}:
  Triple [slf| [n1] - [n2]]
    \[]
    (fun r => \[r = (n1 - n2)])
:= by
  grind

@[grind .]
theorem Triple.mul {n1 n2: Int}:
  Triple [slf| [n1] * [n2]]
    \[]
    (fun r => \[r = (n1 * n2)])
:= by
  grind

@[grind .]
theorem Triple.div {n1 n2: Int}:
  n2 ≠ 0 →
  Triple [slf| [n1] / [n2]]
    \[]
    (fun r => \[r = (n1 / n2)])
:= by
  grind

@[grind .]
theorem Triple.mod {n1 n2: Int}:
  n2 ≠ 0 →
  Triple [slf| [n1] % [n2]]
    \[]
    (fun r => \[r = (n1 % n2)])
:= by
  grind

end Arithmetic

section Comparison

@[grind .]
theorem Triple.eq {n1 n2: Val}:
  Triple [slf| [n1] == [n2]]
    \[]
    (fun r => \[r = (n1 == n2)])
:= by
  apply Triple.binop
  apply EvalBinOp.eq

@[grind .]
theorem Triple.neq {n1 n2: Val}:
  Triple [slf| [n1] != [n2]]
    \[]
    (fun r => \[r = (n1 != n2)])
:= by
  apply Triple.binop
  apply EvalBinOp.neq

@[grind .]
theorem Triple.le {n1 n2: Int}:
  Triple [slf| [n1] <= [n2]]
    \[]
    (fun r => \[r = (decide (n1 ≤ n2))])
:= by
  apply Triple.binop
  apply EvalBinOp.le

@[grind .]
theorem Triple.lt {n1 n2: Int}:
  Triple [slf| [n1] < [n2]]
    \[]
    (fun r => \[r = (decide (n1 < n2))])
:= by
  apply Triple.binop
  apply EvalBinOp.lt

@[grind .]
theorem Triple.ge {n1 n2: Int}:
  Triple [slf| [n1] >= [n2]]
    \[]
    (fun r => \[r = (decide (n1 ≥ n2))])
:= by
  apply Triple.binop
  apply EvalBinOp.ge

@[grind .]
theorem Triple.gt {n1 n2: Int}:
  Triple [slf| [n1] > [n2]]
    \[]
    (fun r => \[r = (decide (n1 > n2))])
:= by
  apply Triple.binop
  apply EvalBinOp.gt

end Comparison

@[grind .]
theorem Triple.ptr_add {p: Loc} {n: Int}:
  Triple [slf| [p] +> [n]]
    \[]
    (fun r => \[r = (p + n)])
:= by
  apply Triple.binop
  apply EvalBinOp.ptr_add
  simp

@[grind .]
theorem Triple.ptr_add_nat {p: Loc} {n: Nat}:
  Triple [slf| [p] +> [n]]
    \[]
    (fun r => \[r = (p + (n: Int))])
:= by
  apply Triple.binop
  apply EvalBinOp.ptr_add
  lia

end PrimitiveOpRules
