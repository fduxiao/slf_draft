import Qq
import SLF.Heap.Tactics.XSimpRStep

namespace SLF.Heap.XSimp
open Lean Elab Tactic Qq XHelpers

section XSimpLRStep

section StarsFlip

scoped elab "hstars_flip": tactic => withMainContext do
  let goal ← getMainGoalQ
  match goal with
  | ~q($lhs = _) =>
    let stars ← splitStar lhs
    let stars := stars.reverse
    let stars ← match stars with
    | ~q(\[]) :: xs => pure (xs ++ [q(\[])])
    | _ => pure stars
    let rhs ← joinStar stars
    let lhs ← delabNoPP lhs
    let rhs ← delabNoPP rhs
    evalTactic <| ← `(tactic| refine @id ($lhs = $rhs) (by hprop_eq) )
  | _ => throwError "hstars_flip failed"

#try {p H2}:
  (forall x Hra, p ~~> x ** H2 ** \[] = Hra → False) →
  False
:= by
  intro H
  apply H
  . hstars_flip
  . exact default

example {H1 H2 H3}:
  (forall {H}, H1 ** H2 ** H3 ** \[] = H → H = H → True) → True
:= by
  intro M
  apply M
  hstars_flip
  rfl

example:
  (forall H, \[] = H → H = H → True) → True
:= by
  intro M
  apply M
  hstars_flip
  rfl

theorem XSimp.change_hra {HL} {Hra Hra' Hrg Hrt}:
  Hra = Hra' →
  XSimp HL (Hra', Hrg, Hrt) →
  XSimp HL (Hra, Hrg, Hrt)
:= by
  grind

macro "xsimp_flip_acc_l": tactic => `(tactic|
  refine XSimp.change_hla (by hstars_flip) ?_
)

macro "xsimp_flip_acc_r": tactic => `(tactic|
  refine XSimp.change_hra (by hstars_flip) ?_
)

macro "xsimp_flip_acc": tactic => `(tactic|
  (try xsimp_flip_acc_l) <;>
  (try xsimp_flip_acc_r)
)

#try {p} {H1 H2 H3 H4: HProp}:
  H1 ** \∃ (n: Int), (p ~~> n ** H2) ** H3 ==> H4
:= by
  xsimp_start
  repeat' xsimp_step_l
  xsimp_step_r
  guard_target =
    XSimp (H3 ** H2 ** p ~~> _ ** H1 ** \[], \[], \[]) (H4 ** \[], \[], \[])
  xsimp_flip_acc  -- this should work even without the `[slf| ... ]` notation
  guard_target =
    XSimp (H1 ** p ~~> _ ** H2 ** H3 ** \[], \[], \[]) (H4 ** \[], \[], \[])
  sorry

#try {H1 H2 H3 H4 H5 H6 H7}:
  XSimp (H4 ** H3 ** H1 ** \[], \[], \[]) (H7 ** H6 ** H5 ** \[], \[], \[])
:= by
  guard_target =
    XSimp (H4 ** H3 ** H1 ** \[], \[], \[]) (H7 ** H6 ** H5 ** \[], \[], \[])
  xsimp_flip_acc_l
  guard_target =
    XSimp (H1 ** H3 ** H4 ** \[], \[], \[]) (H7 ** H6 ** H5 ** \[], \[], \[])
  xsimp_flip_acc_r
  guard_target =
    XSimp (H1 ** H3 ** H4 ** \[], \[], \[]) (H5 ** H6 ** H7 ** \[], \[], \[])
  sorry

open Lang in
#try {H1 H2 p}:
  XSimp (H2 ** H1 ** \[], \[], \[]) (p ~~> ?x ** H2 ** \[], \[], \[])
:= by
  xsimp_flip_acc
  . guard_target =
      XSimp (H1 ** H2 ** \[], \[], \[]) (H2 ** p ~~> ?x ** \[], \[], \[])
    sorry

end StarsFlip

section NecessaryTheorems

theorem XSimp.imp_lr_top {Hla Hrg}:
  XSimp (\[], \[], \[]) (\[], Hrg, \[]) →
  XSimp (Hla, \[], \[]) (\[], (\Top ** Hrg), \[])
:= by
  grind

theorem XSimp.imp_lr_hgc {Hla Hrg}:
  HProp.affine Hla →
  XSimp (\[], \[], \[]) (\[], Hrg, \[]) →
  XSimp (Hla, \[], \[]) (\[], (\GC ** Hrg), \[])
:= by
  grind

theorem XSimp.lr_exit_nogc {Hla Hra}:
  Hla ==> Hra →
  XSimp (Hla, \[], \[]) (Hra, \[], \[])
:= by
  grind

theorem XSimp.lr_exit {Hla Hra Hrg}:
  Hla ==> Hra ** Hrg ->
  XSimp (Hla, \[], \[]) (Hra, Hrg, \[])
:= by
  grind

theorem XSimp.lr_refl {Hla}:
  XSimp (Hla, \[], \[]) (Hla, \[], \[])
:= by
  grind

theorem XSimp.lr_eq {Hla Hra}:
  Hla = Hra →
  XSimp (Hla, \[], \[]) (Hra, \[], \[])
:= by
  grind

theorem XSimp.lr_hwand {H1 H2 Hla}:
  XSimp (\[], \[], (H1 ** Hla)) (\[], \[], H2 ** \[]) →
  XSimp (Hla, \[], \[]) ((H1 -* H2) ** \[], \[], \[])
:= by
  grind

theorem XSimp.lr_wand_false {Hla H1}:
  XSimp (Hla, \[], \[]) ((\[False] -* H1) ** \[], \[], \[])
:= by
  grind

theorem XSimp.lr_qwand {α} {Q1 Q2: α → HProp} {Hla}:
  (forall x, XSimp (\[], \[], (Q1 x ** Hla)) (\[], \[], Q2 x ** \[])) →
  XSimp (Hla, \[], \[]) ((Q1 -** Q2) ** \[], \[], \[])
:= by
  grind

theorem XSimp.lr_qwand_unit {Q1 Q2: Unit → HProp} {Hla}:
  XSimp (\[], \[], (Q1 () ** Hla)) (\[], \[], (Q2 () ** \[])) →
  XSimp (Hla, \[], \[]) ((Q1 -** Q2) ** \[], \[], \[])
:= by
  simp [XSimp]

theorem XSimp.lr_qwand_unify {α} {Q: α → HProp} {Hla}:
  XSimp (Hla, \[], \[]) ((Q -** (Q *+ Hla)) ** \[], \[], \[])
:= by
  grind

theorem XSimp.lr_forall {α} (J:α → HProp) {Hla}:
  (forall x, XSimp (\[], \[], Hla) (\[], \[], J x ** \[])) →
  XSimp (Hla, \[], \[]) ((HProp.forall J) ** \[], \[], \[])
:= by
  simp [XSimp]
  grind

end NecessaryTheorems
section TheTactic

scoped macro "xaffine": tactic => `(tactic| first | (simp_all <;> grind) | try grind)

scoped elab "xsimp_step_lr" : tactic => withMainContext do
  let goal ← getMainGoalQ
  let ⟨lhs, rhs⟩ ← parseXSimp goal
  evalTactic <| ← match lhs, rhs with
  | ~q(($Hla, \[], \[])), ~q(($Hra, $Hrg, \[])) =>
    match Hrg with
    | ~q(\[]) =>
      match Hra with
      | ~q($H1 ** \[]) =>
        match H1 with
        | ~q(\[False] -* $H2) => `(tactic| apply XSimp.lr_wand_false)
        | ~q($H1 -* $H2) => `(tactic| xsimp_flip_acc_l <;> apply XSimp.lr_hwand)
        | ~q($Q1 -** $Q2) =>
          if Q2.isMVar then
            `(tactic| apply XSimp.lr_qwand_unify)
          else
            match H1 with
            | ~q(@HProp.qwand Unit $Q1 $Q2) =>
              `(tactic| xsimp_flip_acc_l <;> apply XSimp.lr_qwand_unit)
            | _ =>
              `(tactic| xsimp_flip_acc_l <;> apply XSimp.lr_qwand <;> intro _)
        | ~q(HProp.forall _) =>
          `(tactic| xsimp_flip_acc_l <;> apply XSimp.lr_hforall <;> intro _)
        | _ =>
          if H1.isMVar then
            `(tactic| apply XSimp.lr_eq (by simp <;> rfl))
          else
            `(tactic| xsimp_flip_acc <;> apply XSimp.lr_exit)
      | ~q(\[]) =>
        `(tactic|
            first |apply XSimp.lr_refl | xsimp_flip_acc <;> apply XSimp.lr_exit_nogc
          )
      | _ =>
        `(tactic| xsimp_flip_acc <;> apply XSimp.lr_exit_nogc)
    | ~q(\Top ** _) => `(tactic| apply XSimp.imp_lr_top)
    | ~q(\GC ** _) => `(tactic| apply XSimp.imp_lr_hgc (by xaffine))
    | _ =>
      `(tactic| xsimp_flip_acc <;> apply XSimp.lr_exit)
  | _, _ =>
    throwError "xsimp_step_lr match failed"

open Lang

example {Q1 Q2 Q': Val → HProp}:
  XSimp ((Q' -** Q1) ** (Q1 -** Q2) ** \[], \[], \[]) ((Q' -** Q2) ** \[], \[], \[])
:= by
  xsimp_step_lr
  guard_target =
    XSimp
      (\[], \[], Q' _ ** (Q1 -** Q2) ** (Q' -** Q1) ** \[])
      (\[], \[], Q2 _ ** \[])
  xsimp_step_l
  xsimp_step_l
  xsimp_step_l
  guard_target =
    XSimp
      (Q' _ ** \[], (Q' -** Q1) ** (Q1 -** Q2) ** \[], \[])
      (\[], \[], Q2 _ ** \[])
  xsimp_step_l
  guard_target =
    XSimp
      (\[], (Q1 -** Q2) ** \[], \[] ** Q1 _ ** \[])
      (\[], \[], Q2 _ ** \[])
  repeat xsimp_step_l
  guard_target =
    XSimp (Q2 _ ** \[], \[], \[]) (\[], \[], Q2 _ ** \[])
  xsimp_step_r
  xsimp_step_lr

#try {H2 H4}:
  XSimp (H2 ** H4 ** \[], \[], \[]) (\[], \[], \[])
:= by
  xsimp_step_lr
  sorry

#try {H1 H2 p}:
  XSimp (H1 ** \[], \[], \[]) (p ~~> [slf| [?x] ] ** H2 ** \[], \[], \[])
:= by
  xsimp_step_lr
  guard_target = H1 ** \[] ==> H2 ** p ~~> ?x ** \[]
  sorry

#try {H1 H2 H3 H4}:
  XSimp (H3 ** H2 ** H1 ** \[], \[], \[]) (H4 ** \[], \[], \[])
:= by
  xsimp_step_lr
  guard_target = H1 ** H2 ** H3 ** \[] ==> (H4 ** \[]) ** \[]
  sorry

#try {H1 H2 H3 H4} {p} {n: Int}:
  XSimp (H3 ** H2 ** p ~~> [slf| [n] ] ** H1 ** \[], \[], \[]) (H4 ** \[], \[], \[])
:= by
  xsimp_step_lr
  guard_target = H1 ** p ~~> [slf| [n] ] ** H2 ** H3 ** \[] ==> (H4 ** \[]) ** \[]
  sorry

#try {p} {H1 H2 H3 H4: HProp}:
  H1 ** \∃ (n: Int), (p ~~> n ** H2) ** H3 ==> H4
:= by
  xsimp_start
  repeat' xsimp_step_l
  xsimp_step_r
  xsimp_step_lr
  guard_target = H1 ** p ~~> [slf| [n] ] ** H2 ** H3 ** \[] ==> (H4 ** \[]) ** \[]
  sorry

scoped macro "xsimp_step" b:bool : tactic => `(tactic|
  first | xsimp_step_l $b | xsimp_step_r| xsimp_step_lr
)

scoped macro "xsimp_step" : tactic => `(tactic| xsimp_step true)

end TheTactic
end XSimpLRStep

section XSimpPost

scoped macro "xsimp_clean": tactic => `(tactic|
  (try simp only [HProp.star_empty_left, HProp.star_empty_right]) <;>
  (try xsimp_hint_clear)
)

scoped macro "xsimpl_before_generalize": tactic => `(tactic| skip)
scoped macro "xsimp_after_generalize": tactic => `(tactic| skip)

scoped macro "xsimp_generalize": tactic => `(tactic|(
  xsimpl_before_generalize <;>
  (try contradiction) <;>
  (revert_after_mark) <;>
  -- (clear_mark!) <;>
  xsimp_after_generalize
))

scoped macro "xsimp_post": tactic => `(tactic| xsimp_clean <;> xsimp_generalize)

end XSimpPost

section XSimpTactic

scoped macro "xsimp": tactic => `(tactic|
  (xsimp_start <;> (repeat' xsimp_step) <;> xsimp_post; clear_mark')
)

scoped macro "xsimp" "[" ts:term,+ "]"?: tactic => `(tactic| xsimp_hint_put $[$ts],* <;> xsimp)

end XSimpTactic

section XPull

theorem xpull_protect {H1 H2}:
  H1 ==> Protect H2 →
  H1 ==> H2
:= by
  grind

theorem xpull_simp_protect {H: HProp}:
  Protect H = H
:= by
  grind

scoped macro "xpull_start" : tactic => `(tactic|
  tactic_mark <;>
  (try simp only [HProp.star_empty_left, HProp.star_empty_right]) <;>
  intros <;>
  apply xpull_protect <;>
  xsimpl_handle_qimpl <;>
  rw [XSimp.intro]
)

scoped macro "xpull_post" : tactic => `(tactic|
  xsimp_clean <;>
  simp only [xpull_simp_protect] <;>
  xsimp_generalize
)

scoped macro "xpull" : tactic => `(tactic|
  (xpull_start <;> (repeat' xsimp_step) <;> xpull_post; clear_mark')
)

end XPull

section Examples

#try {H1 H2 H3 H4: HProp} (n:Int):
  \[n > 1] ** H1 ** H2 ** \[n > 0] ** H3 ==> H4
:= by
  xsimp
  guard_target = n > 1 → n > 0 → H1 ** H2 ** H3 ==> H4
  sorry

example {H1 H2 H3 H4: HProp}:
  H1 ** H2 ** \[False] ** H3 ==> H4
:= by
  xsimp

#try {p} {H1 H2 H3 H4: HProp}:
  H1 ** \∃ (n: Int), (p ~~> n ** H2) ** H3 ==> H4
:= by
  xsimp
  guard_target = ∀ (n : Int), H1 ** p ~~> _ ** H2 ** H3 ==> H4
  sorry

#try {H1 H2 H3 H4 p q}:
  H1 ** \∃ (n: Int), (p ~~> n ** \[n > 0] ** H2) ** \[p != q] ** H3 ==> H4
:= by
  xsimp
  guard_target = ∀ (n : Int), n > 0 → (p != q) = true → H1 ** p ~~> _ ** H2 ** H3 ==> H4
  sorry

#try {H1 H2 H3 H4 H5 H6 H7}:
  H1 ** H2 ** H3 ** H4 ==> H5 ** H6 ** H2 ** H7
:= by
  xsimp
  guard_target = H1 ** H3 ** H4 ==> H5 ** H6 ** H7
  sorry

#try {H1 H2 H3 H4 H5}:
  H1 ** H2 ** H3 ** H4 ==> H4 ** H3 ** H5 ** H2
:= by
  xsimp
  guard_target = H1 ==> H5
  sorry

example {H1 H2 H3 H4}:
  H1 ** H2 ** H3 ** H4 ==> H4 ** H1 ** H2 ** H3
:= by
  xsimp

#try {H1 H2 H3} {n: Int}:
  H1 ==> H2 ** \[n > 0] ** H3
:= by
  xsimp
  . guard_target = n >0
    sorry
  . guard_target = H1 ==> H2 ** H3
    sorry

#try {H1 H2 H3 H4 p}:
  H1 ==> H2 ** \∃ (n: Int), (p ~~> n ** H3) ** H4
:= by
  xsimp
  guard_target = H1 ==> H2 ** p ~~> ?n ** H3 ** H4
  . guard_target = H1 ==> H2 ** p ~~> ?n ** H3 ** H4
    sorry
  . guard_target = Int
    sorry

#try {H1 H2 H3 H4 p}:
  (\∃ n, \[n > 0]) ** H1 ==> H2 ** \∃ (n: Int), (p ~~> n ** H3) ** H4
:= by
  xsimp
  . guard_target = ∀ (n : Nat) (a : n > 0), H1 ==> H2 ** p ~~> _ ** H3 ** H4
    sorry
  . guard_target = (n : Nat) → n > 0 → Int
    sorry

#try {H1 H2 H3 H4} {p}:
  H1 ** (p ~~> 3) ==> H2 ** \∃ (n: Int), (p ~~> n ** H3) ** H4
:= by
  xsimp
  guard_target = H1 ==> H2 ** H3 ** H4
  sorry

#try {H1 H2 H4} {p}:
  H1 ** (p ~~> 3) ==> H2 ** \∃ (n: Int), (p ~~> n ** \[n > 0]) ** H4
:= by
  xsimp
  . guard_target =~ (3: Int) > 0
    sorry
  . guard_target = H1 ==> H2 ** H4
    sorry

example {p}:
  p ~~> 3 ==>
  \∃ (n: Int), (p ~~> n ** \[n > 0])
:= by
  xsimp
  guard_target =~ (3: Int) > 0
  lia

example {p q}:
  p ~~> 3 ** q ~~> 3 ==>
  \∃ (n: Int), p ~~> n ** q ~~> n
:= by
  xsimp

open Lang

#try {H1 p q}:
  H1 ==> \∃ (n m: Int), (p ~~> n ** q ~~> m)
:= by
  xsimp [8, 9]
  guard_target =~ H1 ==> p ~~> [slf| 8 ] ** q ~~> [slf| 9 ]
  sorry

#try {H1 p q}:
  H1 ==> \∃ (n m: Int), (p ~~> n ** q ~~> m)
:= by
  xsimp [_, 9]
  . guard_target = H1 ==> p ~~> _ ** q ~~> [slf| 9 ]
    sorry
  . guard_target = Int
    sorry

#try {H1 p q}:
  (\∃ z, \[z > 0]) ** H1 ==> \∃ (n m: Int), (p ~~> n ** q ~~> m)
:= by
  xsimp [_, 9]
  . guard_target = ∀ (z : Nat) (a : z > 0), H1 ==> p ~~> _ ** q ~~> [slf| 9 ]
    sorry
  . guard_target = (z : Nat) → z > 0 → Int
    sorry

#try {Q1 Q2: Val → HProp} {H2 H3}:
  Q1 *+ H2 ===> Q2 *+ H2 *+ H3
:= by
  xsimp
  guard_target = ∀ (a : Val), Q1 a ==> Q2 a ** H3
  sorry

/-!
xpull
-/
#try {p}:
  \∃ (n: Int), p ~~> n ==>
  \∃ (m: Int), p ~~> (m + 1: Int)
:= by
  xpull
  guard_target = ∀ (n : Int), p ~~> [slf| [n] ] ==> \∃ m, p ~~> [slf| [(m + 1: Int)] ]
  sorry

example {H}:
  \[False] ==> H
:= by
  xpull

#try {p}:
  \∃ (n: Int), p ~~> n ==>
  \∃ (m: Int), p ~~> (m + 1: Int)
:= by
  xpull
  guard_target = ∀ (n : Int), p ~~> [slf| [n] ] ==> \∃ m, p ~~> [slf| [(m + 1: Int)] ]
  intro n
  guard_target = p ~~> [slf| [n] ] ==> \∃ m, p ~~> [slf| [(m + 1: Int)] ]
  xsimp [n-1]
  guard_target = n = n - 1 + 1
  lia

/-
wands
-/

#try {H1 H2 H3 H4 H5}:
  H2 ** H1 ** (H2 -* H3) ** H4 ==> H5
:= by
  xsimp
  guard_target = H4 ** H1 ** H3 ==> H5
  sorry

#try {H1 H2 H3 H4 H5}:
  H1 ** (H2 -* H3) ** H4 ==> H5
:= by
  xsimp
  guard_target = H1 ** H4 ** (H2 -* H3) ==> H5
  sorry

#try {H1 H2 H3 H4}:
  H3 ** H1 ** H4 ** (H1 -* H2) ==> H3
:= by
  xsimp
  guard_target = H4 ** H2 ==> \[]
  sorry

example {Q1 Q2: Val → HProp} {F: (Val → HProp) → HProp}:
  (\∃ Q', F Q' ** (Q' -** Q1)) ** (Q1 -** Q2) ==> \∃ Q', F Q' ** (Q' -** Q2)
:= by
  xsimp

end Examples
