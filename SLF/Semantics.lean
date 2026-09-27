import SLF.Lang

namespace SLF.Lang
open Map

abbrev Heap := FMap Loc Val


def Term.isValue : Term → Bool
  | Term.val _ => true
  | _ => false


/-- Substitution for terms -/
def Term.subst (y: Var) (v: Val) (t: Term): Term :=
  match t with
  | .val v' => .val v'
  | .var x => if x = y then (.val v) else t
  | .fun x t => .fun x $ if x = y then t else (Term.subst y v t)
  | .fix f x t => .fix f x $ if f = y then t else (if x = y then t else (Term.subst y v t))
  | .app t1 t2 => .app (Term.subst y v t1) (Term.subst y v t2)
  | .seq t1 t2 => .seq (Term.subst y v t1) (Term.subst y v t2)
  | .let x t1 t2 => .let x (Term.subst y v t1) (if x = y then t2 else (Term.subst y v t2))
  | .if t0 t1 t2 => .if (Term.subst y v t0) (Term.subst y v t1) (Term.subst y v t2)


/-!
## Small-step semantics of the language
-/
inductive Step: Heap → Term → Heap → Term → Prop where
  -- Context rules
  | seq_ctx {s1 s2 t1 t1' t2}:
      Step s1 t1 s2 t1' →
      Step s1 (.seq t1 t2) s2 (.seq t1' t2)
  | let_ctx {s1 s2 x t1 t1' t2}:
      Step s1 t1 s2 t1' →
      Step s1 (.let x t1 t2) s2 (.let x t1' t2)
  | app_arg1 {s1 s2 t1 t1' t2}:
      Step s1 t1 s2 t1' →
      Step s1 (.app t1 t2) s2 (.app t1' t2)
  | app_arg2 {s1 s2 v1 t2 t2'}:
      Step s1 t2 s2 t2' →
      Step s1 (.app v1 t2) s2 (.app v1 t2')
  -- Reductions
  | fun {s x t}:
      Step s (.fun x t) s (.val (.fun x t))
  | fix {s f x t}:
      Step s (.fix f x t) s (.val (.fix f x t))
  | app_fun {s} {v1 v2: Val} {x t}:
      v1 = .fun x t →
      Step s (.app v1 v2) s (Term.subst x v2 t)
  | app_fix {s} {v1 v2: Val} {f x t}:
      v1 = .fix f x t →
      Step s (.app v1 v2) s (Term.subst x v2 (Term.subst f v1 t))
  | if {s b t1 t2}:
      Step s (.if (.val (.bool b)) t1 t2) s (if b then t1 else t2)
  | seq {s t2 v1}:
      Step s (.seq (.val v1) t2) s t2
  | let {s x t2 v1}:
      Step s (.let x (.val v1) t2) s (Term.subst x v1 t2)
  -- Unary operations
  | neg {s} {b: Bool}:
      Step s [slf| not [b] ] s [slf| [not b] ]
  | opp {s} {n: Int}:
      Step s [slf| - [n] ] s [slf| [(- n: Int)] ]
  | rand {s} {n n1: Int}:
      0 ≤ n1 →
      n1 < n →
      Step s ([slf| rand [n] ]) s [slf| [n1] ]
  -- Binary operations
  | eq {s} {v1 v2: Val}:
      Step s [slf| [v1] == [v2] ] s [slf| [v1 == v2] ]
  | neq {s} {v1 v2: Val}:
      Step s [slf| [v1] != [v2] ] s [slf| [v1 != v2] ]
  | add {s} {n1 n2: Int}:
      Step s [slf| [n1] + [n2] ] s [slf| [n1 + n2] ]
  | sub {s} {n1 n2: Int}:
      Step s [slf| [n1] - [n2] ] s [slf| [n1 - n2] ]
  | mul {s} {n1 n2: Int}:
      Step s [slf| [n1] * [n2] ] s [slf| [n1 * n2] ]
  | div {s} {n1 n2: Int}:
      n2 ≠ 0 →
      Step s [slf| [n1] / [n2] ] s [slf| [n1 / n2] ]
  | mod {s} {n1 n2: Int}:
      n2 ≠ 0 →
      Step s [slf| [n1] % [n2] ] s [slf| [n1 % n2] ]
  | le {s} {n1 n2: Int}:
      Step s [slf| [n1] <= [n2] ] s [slf| [decide (n1 ≤ n2)] ]
  | lt {s} {n1 n2: Int}:
      Step s [slf| [n1] < [n2] ] s [slf| [decide (n1 < n2)] ]
  | ge {s} {n1 n2: Int}:
      Step s [slf| [n1] >= [n2] ] s [slf| [decide (n1 ≥ n2)] ]
  | gt {s} {n1 n2: Int}:
      Step s [slf| [n1] > [n2] ] s [slf| [decide (n1 > n2)] ]
  | ptr_add {s} {p1 p2: Loc} {n: Int}:
      p2.toInt = (p1 + n).toInt →
      Step s [slf| [.loc p1] +> [n] ] s [slf| [.loc p2] ]
  -- Heap operations
  | ref {s: Heap} {p: Loc} {v: Val}:
      ¬ p ∈ s →
      Step s [slf| ref [v] ] (s[ p => v ]) [slf| [p] ]
  | get {s: Heap} {p: Loc}:
      p ∈ s →
      Step s [slf| get [p] ] s s[p]!
  | set {s: Heap} {p: Loc} {v: Val}:
      p ∈ s →
      Step s [slf| set [p] [v] ] (s[p => v]) [slf| val_unit]
  | free {s: Heap} {p: Loc}:
      p ∈ s →
      Step s [slf| free [p] ] (s ÷ p) [slf| val_unit]


inductive MStep: Heap → Term → Heap → Term → Prop where
  | refl {s t}: MStep s t s t
  | step {s1 s2 s3 t1 t2 t3}:
      Step s1 t1 s2 t2 →
      MStep s2 t2 s3 t3 →
      MStep s1 t1 s3 t3


theorem MStep.ofStep {s1 s2 t1 t2}:
  Step s1 t1 s2 t2 →
  MStep s1 t1 s2 t2
:= by
  intro H
  apply MStep.step H
  apply MStep.refl


instance (s1 t1 s2 t2): Coe (Step s1 t1 s2 t2) (MStep s1 t1 s2 t2) where
  coe := MStep.ofStep


theorem MStep.trans {s1 s2 s3 t1 t2 t3}:
  MStep s1 t1 s2 t2 →
  MStep s2 t2 s3 t3 →
  MStep s1 t1 s3 t3
:= by
  intro H1 H2
  induction H1
  case refl =>
    exact H2
  case step s1 s1' s2 t1 t1' t2 H11' H1'2 IH =>
    specialize IH H2
    apply MStep.step
    . exact H11'
    . exact IH


def Term.reducible (s: Heap) (t: Term): Prop :=
  ∃ s' t', Step s t s' t'


def Term.nonstuck (s: Heap) (t: Term): Prop :=
  t.isValue ∨ Term.reducible s t


/-!
## Omni-Big-step semantics of the language
-/

/-- EvalUnOp `op v P` means that `op v` evaluates to a value that satisfies `P`. -/
inductive EvalUnOp : Prim → Val → (Val → Prop) → Prop where
  | neg {b: Bool}:
      EvalUnOp .neg b (· = !b)
  | opp {n: Int}:
      EvalUnOp .opp n (· = (- n: Int))
  | rand {n: Int}:
      0 < n →
      EvalUnOp .rand n (fun r => ∃ n1: Int, r = n1 ∧ 0 ≤ n1 ∧ n1 < n)


/-- EvalBinOp `op v1 v2 P` means that `op v1 v2` evaluates to a value that satisfies `P`. -/
inductive EvalBinOp : Prim → Val → Val → (Val → Prop) → Prop where
  | eq {v1 v2: Val}:
      EvalBinOp .eq v1 v2 (· = (v1 == v2))
  | neq {v1 v2: Val}:
      EvalBinOp .neq v1 v2 (· = (v1 != v2))
  | add {n1 n2: Int}:
      EvalBinOp .add n1 n2 (· = (n1 + n2))
  | sub {n1 n2: Int}:
      EvalBinOp .sub n1 n2 (· = (n1 - n2))
  | mul {n1 n2: Int}:
      EvalBinOp .mul n1 n2 (· = (n1 * n2))
  | div {n1 n2: Int}:
      n2 ≠ 0 →
      EvalBinOp .div n1 n2 (· = (n1 / n2))
  | mod {n1 n2: Int}:
      n2 ≠ 0 →
      EvalBinOp .mod n1 n2 (· = (n1 % n2))
  | le {n1 n2: Int}:
      EvalBinOp .le n1 n2 (· = (decide (n1 ≤ n2)))
  | lt {n1 n2: Int}:
      EvalBinOp .lt n1 n2 (· = (decide (n1 < n2)))
  | ge {n1 n2: Int}:
      EvalBinOp .ge n1 n2 (· = (decide (n1 ≥ n2)))
  | gt {n1 n2: Int}:
      EvalBinOp .gt n1 n2 (· = (decide (n1 > n2)))
  | ptr_add {p1 p2: Loc} {n: Int}:
      p2.toInt = (p1 + n).toInt →
      EvalBinOp .ptr_add p1 n (· = p2)

/--
`PurePost s P` converts a predicate `P: Val → Prop` into
a postcondition of type `Val → Heap → Prop` that holds in the state `s`.
-/
def PurePost (s: Heap) (P: Val → Prop): Val → Heap → Prop := fun v s' => P v ∧ s = s'

/--
equivalent to `PurePost s P ===> Q`
-/
def PurePostIn (s: Heap) (P: Val → Prop) (Q: Val → Heap → Prop): Prop := ∀ v, P v → Q v s


inductive Eval : Heap → Term → (Val → Heap → Prop) → Prop where
  | val {s} {v} {Q}:
      Q v s →
      Eval s (.val v) Q
  | fun {s x t Q}:
      Q (.fun x t) s →
      Eval s (.fun x t) Q
  | fix {s f x t Q}:
      Q (.fix f x t) s →
      Eval s (.fix f x t) Q
  | app1 {s1 t1 t2 Q1 Q}:
      ¬ t1.isValue →
      Eval s1 t1 Q1 →
      (∀ v1 s2, Q1 v1 s2 → Eval s2 (.app v1 t2) Q) →
      Eval s1 (.app t1 t2) Q
  | app2 {s1} {v1: Val} {t2 Q1 Q}:
      ¬ t2.isValue →
      Eval s1 t2 Q1 →
      (∀ v2 s2, Q1 v2 s2 → Eval s2 (.app v1 v2) Q) →
      Eval s1 (.app v1 t2) Q
  | app_fun {s1} {v1 v2: Val} {x t1 Q}:
      v1 = .fun x t1 →
      Eval s1 (Term.subst x v2 t1) Q →
      Eval s1 (.app v1 v2) Q
  | app_fix {s} {v1 v2: Val} {f x t1 Q}:
      v1 = .fix f x t1 →
      Eval s (Term.subst x v2 (Term.subst f v1 t1)) Q →
      Eval s (.app v1 v2) Q
  | seq {s1 t1 t2 Q1 Q}:
      Eval s1 t1 Q1 →
      (∀ v1 s2, Q1 v1 s2 → Eval s2 t2 Q) →
      Eval s1 (.seq t1 t2) Q
  | let {Q1 s1 x t1 t2 Q}:
      Eval s1 t1 Q1 →
      (∀ v1 s2, Q1 v1 s2 → Eval s2 (Term.subst x v1 t2) Q) →
      Eval s1 (.let x t1 t2) Q
  | if {s} {b: Bool} {t1 t2 Q}:
      Eval s (if b then t1 else t2) Q →
      Eval s (.if b t1 t2) Q
  | unop {op s v1 P Q}:
      EvalUnOp op v1 P →
      PurePostIn s P Q →
      Eval s (.app op v1) Q
  | binop {op s v1 v2 P Q}:
      EvalBinOp op v1 v2 P →
      PurePostIn s P Q →
      Eval s (.app (.app op v1) v2) Q
  | ref {s} {v: Val} {Q}:
      (∀ p: Loc, ¬ p ∈ s →
          Q (.loc p) (s[p => v])) →
      Eval s ([slf| ref [v] ]) Q
  | get {s: Heap} {p: Loc} {Q}:
      p ∈ s →
      Q s[p]! s →
      Eval s [slf| ![p] ] Q
  | set {s: Heap} {p: Loc} {v: Val} {Q}:
      p ∈ s →
      Q .unit (s[p => v]) →
      Eval s [slf| [p] := [v] ] Q
  | free {s: Heap} {p: Loc} {Q}:
      p ∈ s →
      Q .unit (s ÷ p) →
      Eval s [slf| free [p] ] Q


theorem Eval.val_minimal {s v}:
  Eval s (.val v) (PurePost s (· = v))
:=
  Eval.val (by simp [PurePost])


theorem Eval.add {s} {n1 n2: Int} {Q: Val → Heap → Prop}:
  Q (n1 + n2) s →
  Eval s [slf| [n1] + [n2] ] Q
:= by
  intro H
  apply Eval.binop .add
  simp [PurePostIn]
  exact H


theorem Eval.sub {s} {n1 n2: Int} {Q: Val → Heap → Prop}:
  Q (n1 - n2) s →
  Eval s [slf| [n1] - [n2] ] Q
:= by
  intro H
  apply Eval.binop .sub
  simp [PurePostIn]
  exact H


theorem Eval.mul {s} {n1 n2: Int} {Q: Val → Heap → Prop}:
  Q (n1 * n2) s →
  Eval s [slf| [n1] * [n2] ] Q
:= by
  intro H
  apply Eval.binop .mul
  simp [PurePostIn]
  exact H


theorem Eval.div {s} {n1 n2: Int} {Q: Val → Heap → Prop}:
  n2 ≠ 0 →
  Q (n1 / n2) s →
  Eval s [slf| [n1] / [n2] ] Q
:= by
  intro Hn2 H
  apply Eval.binop (.div Hn2)
  simp [PurePostIn]
  exact H


theorem Eval.mod {s} {n1 n2: Int} {Q: Val → Heap → Prop}:
  n2 ≠ 0 →
  Q (n1 % n2) s →
  Eval s [slf| [n1] % [n2] ] Q
:= by
  intro Hn2 H
  apply Eval.binop (.mod Hn2)
  simp [PurePostIn]
  exact H


theorem Eval.rand {s} {n: Int} {Q: Val → Heap → Prop}:
  0 < n →
  (∀ n1: Int, 0 ≤ n1 → n1 < n → Q n1 s) →
  Eval s [slf| rand [n] ] Q
:= by
  intro Hn H
  apply Eval.unop (.rand Hn)
  simp_all [PurePostIn]


/--
`Eval.app1` requires that the first argument is not a value.
This is a bit inconvenient, so we provide a version that does not require this.
```lean
app1 {s1 t1 t2 Q1 Q}:
  ¬ t1.isValue →
  Eval s1 t1 Q1 →
  (∀ v1 s2, Q1 v1 s2 → Eval s2 (.app v1 t2) Q) →
  Eval s1 (.app t1 t2) Q
```
-/
theorem Eval.app1' {s1 t1 t2 Q1 Q}:
  Eval s1 t1 Q1 →
  (∀ v1 s2, Q1 v1 s2 → Eval s2 (.app v1 t2) Q) →
  Eval s1 (.app t1 t2) Q
:= by
  intro H1 H2
  cases E: t1.isValue with
  | false =>
    apply Eval.app1
    . simp_all
    . exact H1
    . exact H2
  | true =>
    cases t1 <;> try contradiction
    simp [Term.isValue] at E
    cases H1
    apply H2
    assumption


/--
Theorem `Eval.app2` requires that the second argument is not a value.
This is a bit inconvenient, so we provide a version that does not require this.
```lean
app2 {s1} {v1: Val} {t2 Q1 Q}:
  ¬ t2.isValue →
  Eval s1 t2 Q1 →
  (∀ v2 s2, Q1 v2 s2 → Eval s2 (.app v1 v2) Q) →
  Eval s1 (.app v1 t2) Q
```
-/
theorem Eval.app2' {s1} {v1: Val} {t2 Q1 Q}:
  Eval s1 t2 Q1 →
  (∀ v2 s2, Q1 v2 s2 → Eval s2 (.app v1 v2) Q) →
  Eval s1 (.app v1 t2) Q
:= by
  intro H1 H2
  cases E: t2.isValue with
  | false =>
    apply Eval.app2
    . simp_all
    . exact H1
    . exact H2
  | true =>
    cases t2 <;> try contradiction
    simp [Term.isValue] at E
    cases H1
    apply H2
    assumption


def Term.eval_like (t1 t2: Term): Prop :=
  ∀ s Q, Eval s t1 Q → Eval s t2 Q


@[refl]
theorem Term.eval_like.refl {t}:
  Term.eval_like t t
:= by
  simp [Term.eval_like]
