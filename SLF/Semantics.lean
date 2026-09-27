import SLF.Lang

namespace SLF.Lang
open Map

abbrev Heap := FMap Loc Val


def Term.isValue : Term → Prop
  | Term.val _ => True
  | _ => False


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
