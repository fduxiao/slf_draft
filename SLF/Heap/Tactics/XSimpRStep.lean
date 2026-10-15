import Qq
import SLF.Heap.Heap
import SLF.Heap.Tactics.HPropEq
import SLF.Heap.Tactics.XSimpLStep

namespace SLF.Heap.XSimp

section NecessaryTheorems

theorem XSimp.right_empty {Hra Hrg Hrt HL}:
  XSimp HL (Hra, Hrg, Hrt) →
  XSimp HL (Hra, Hrg, \[] ** Hrt)
:= by
  grind

theorem XSimp.right_wand_same {H Hra Hrg Hrt HL}:
  XSimp HL (Hra, Hrg, Hrt) →
  XSimp HL (Hra, Hrg, (H -* H) ** Hrt)
:= by
  simp only [XSimp]
  intro K
  calc
    _ ==> Hra ** Hrg ** Hrt := K
    _ ==> Hra ** Hrg ** (\[] ** Hrt) := by simp
    _ ==> _ := by
      apply HProp.imp_frame_right
      apply HProp.imp_frame_right
      apply HProp.imp_frame_left
      exact HProp.imp_empty_wand_same

theorem XSimp.right_pure {P Hra Hrg Hrt HL}:
  P →
  XSimp HL (Hra, Hrg, Hrt) ->
  XSimp HL (Hra, Hrg, \[P] ** Hrt)
:= by
  grind

theorem XSimp.right_flatten {Hra Hrg H1 H2 H3 L}:
  XSimp L (Hra, Hrg, (H1 ** H2) ** H3) ↔
  XSimp L (Hra, Hrg, H1 ** (H2 ** H3))
:= by
  grind

theorem XSimp.right_keep {H Hra Hrg Hrt HL}:
  XSimp HL (H ** Hra, Hrg, Hrt) →
  XSimp HL (Hra, Hrg, H ** Hrt)
:= by
  simp [XSimp]
  grind

/-!
`\GC` and `\Top` are handled specially in the XSimp right step.
-/

theorem XSimp.right_gc_or_top {H Hra Hrg Hrt HL}:
  XSimp HL (Hra, H ** Hrg, Hrt) →
  XSimp HL (Hra, Hrg, H ** Hrt)
:= by
  grind

theorem XSimp.lr_cancel_gc  {Hla Hlw Hlt Hra Hrg Hrt}:
  XSimp (Hla, Hlw, Hlt) (Hra, \GC ** Hrg, Hrt) →
  XSimp (\GC ** Hla, Hlw, Hlt) (Hra, \GC ** Hrg, Hrt)
:= by
  grind

theorem XSimp.lr_cancel_top {H Hla Hlw Hlt Hra Hrg Hrt}:
  XSimp (Hla, Hlw, Hlt) (Hra, \Top ** Hrg, Hrt) →
  XSimp (H ** Hla, Hlw, Hlt) (Hra, \Top ** Hrg, Hrt)
:= by
  simp [XSimp]
  intro M
  himp_change_rhs \Top ** Hra ** Hrg ** Hrt at M := by hprop_eq
  himp_change_rhs \Top ** \Top ** Hra ** Hrg ** Hrt := by hprop_eq
  apply HProp.imp_frame_lr
  . simp
  . exact M

theorem XSimp.lr_cancel_same {H Hla Hlw Hlt Hra Hrg Hrt}:
  XSimp (Hla, Hlw, Hlt) (Hra, Hrg, Hrt) →
  XSimp ((H ** Hla), Hlw, Hlt) (Hra, Hrg, (H ** Hrt))
:= by
  grind

theorem XSimp.right_top_replace_gc {Hra Hrg Hrt HL}:
  XSimp HL (Hra, (\Top ** Hrg), Hrt) →
  XSimp HL (Hra, (\GC ** Hrg), (\Top ** Hrt))
:= by
  grind

theorem XSimp.right_gc_drop {Hra Hrg Hrt HL}:
  XSimp HL (Hra, Hrg, Hrt) →
  XSimp HL (Hra, Hrg, (\GC ** Hrt))
:= by
  simp only [XSimp]
  intro H
  calc
    _ ==> Hra ** Hrg ** (\[] ** Hrt) := by simp; exact H
    _ = Hra ** Hrg ** (\[] ** Hrt) := by rfl
  apply HProp.imp_frame_right
  apply HProp.imp_frame_right
  apply HProp.imp_frame_left
  apply HProp.top_terminal

theorem XSimp.right_top_drop {Hra Hrg Hrt HL}:
  XSimp HL (Hra, Hrg, Hrt) →
  XSimp HL (Hra, Hrg, (\Top ** Hrt))
:= by
  apply XSimp.right_gc_drop

theorem XSimp.right_exists  {α} {x:α} {J:α → HProp} {Hra Hrg Hrt HL}:
  XSimp HL (Hra, Hrg, (J x ** Hrt)) →
  XSimp HL (Hra, Hrg, (\∃[J] ** Hrt))
:= by
  simp only [XSimp]
  intro H
  refine H.trans ?_
  apply HProp.imp_frame_right
  apply HProp.imp_frame_right
  apply HProp.imp_frame_left
  simp

end NecessaryTheorems

section XSimpRStepCore
open Lean Meta Elab Tactic Qq XHelpers

def XHelpers.matchRhs (rhs: Q(HProp × HProp × HProp)): MetaM (Q(HProp) × Q(HProp) × Q(HProp) × Q(HProp)) := do
  match rhs with
  | ~q(($Hra, $Hrg, $H ** $Hrt)) => pure (Hra, Hrg, H, Hrt)
  | _ => throwError m!"unexpected RHS structure {rhs}"

macro "xsimpl_hgc_or_htop_cancel" t:term "by" th:term: tactic =>
  `(tactic| repeat( xsimp_pick_same $t <;> apply $th ))

macro "xsimp_cancel_same" t:term: tactic =>
  `(tactic| xsimp_pick_same $t <;> apply XSimp.lr_cancel_same)

def XHelpers.gcOrTop (Hrg H: Q(HProp)) : MetaM (TSyntax `tactic) := do
  match Hrg, H with
  | ~q(\[]), ~q(\GC) =>
    `(tactic|
      apply XSimp.right_gc_or_top <;> xsimpl_hgc_or_htop_cancel (\GC) by XSimp.lr_cancel_gc
    )
  | ~q(\[]), ~q(\Top) =>
    `(tactic|
      apply XSimp.right_gc_or_top <;>
      xsimpl_hgc_or_htop_cancel (\GC) by XSimp.lr_cancel_gc <;>
      xsimpl_hgc_or_htop_cancel (\Top) by XSimp.lr_cancel_top
    )
  | ~q(\GC ** \[]), ~q(\Top) =>
    `(tactic|
      apply XSimp.right_top_replace_gc <;>
      xsimpl_hgc_or_htop_cancel (\Top) by XSimp.lr_cancel_top
    )
  | ~q(\GC ** \[]), ~q(\GC) => `(tactic|apply XSimp.right_gc_drop)
  | ~q(\Top ** \[]), ~q(\GC) => `(tactic|apply XSimp.right_gc_drop)
  | ~q(\Top ** \[]), ~q(\Top) => `(tactic|apply XSimp.right_top_drop)
  | _, _ => throwError m!"unexpected gc or top structure {Hrg} {H}"

scoped elab "xsimp_step_r_core": tactic => withMainContext do
  let goal ← getMainGoalQ
  let ⟨lhs, rhs⟩ ← parseXSimp goal
  let ⟨Hra, Hrg, H, Hrt⟩ ← matchRhs rhs
  evalTactic <| ← match H with
    | ~q(\[]) => `(tactic| apply XSimp.right_empty)
    | ~q(\[$H]) => `(tactic| apply XSimp.right_pure)
    | ~q($H1 ** $H2) => `(tactic| rw [XSimp.right_flatten])
    | ~q($H -* $H') =>
      match H with
      | ~q(\[$P]) => throwError m!"don't cancel out cause \\[{P}] might contain a contradiction"
      | _ =>
        if H' == H then
          `(tactic| apply XSimp.right_wand_same)
        else
          throwError m!"unexpected wand structure {H} -* {H'}"
    | ~q(HProp.exists $P) =>
      --   | hexists ?J => xsimpl_r_hexists_apply tt
      throwError m!"unexpected exists structure {H}"
    | ~q(\GC) => gcOrTop Hrg H
    | ~q(\Top) => gcOrTop Hrg H
    | ~q(Protect $H) => `(tactic| apply XSimp.right_keep)
    | ~q(@Protect ($α → HProp) $Q $x) => `(tactic| apply XSimp.right_keep)
    | ~q($p ~> $v) =>
      -- I don't understand the usage of `repr` now, so let's just throw an error.
      throwError m!"unexpected repr structure {p} ~> {v}"
    | _ =>
      if H.isMVar then
        `(tactic | first | xsimp_hook | apply XSimp.right_keep)
      else
        let stx ← PrettyPrinter.delab H
        `(tactic | first | xsimp_cancel_same $stx | xsimp_hook | apply XSimp.right_keep)

macro "xsimp_step_r" : tactic => `(tactic| xsimp_step_r_core)
end XSimpRStepCore

section Examples

#try {H1 H2 H3}:
  H1 ** \GC ** H2 ** H3 ==> H1 ** \GC ** H2 ** H3
:= by
  xsimp_start
  repeat xsimp_step_l
  xsimp_step_r
  xsimp_step_r
  xsimp_step_r
  xsimp_step_r
  xsimp_step_r
  xsimp_step_r
  xsimp_step_r
  sorry

#try {H1 H2 H3}:
  H1 ** H2 ** H3 ==> H2 ** H1 ** H1
:= by
  xsimp_start
  repeat xsimp_step_l
  xsimp_step_r
  xsimp_step_r
  xsimp_step_r
  xsimp_step_r
  xsimp_step_r
  sorry

example {H1 H2 H3 H4}:
  H1 ** H2 ** H3 ** H4 ==> H4 ** H3 ** H1 ** H2
:= by
  xsimp_start
  repeat xsimp_step_l
  repeat' xsimp_step_r
  simp [XSimp]

#try {H1 H2 H3} {P}:
  H1 ** H2 ** H3 ==> \[P] ** H2 ** H1 ** H1
:= by
  xsimp_start
  repeat xsimp_step_l
  repeat' xsimp_step_r
  sorry
  sorry

#try {H1 H2 H3} {n: Nat}:
  H1 ** H2 ** H3 ==> \[n > 3] ** H2 ** H1 ** H1
:= by
  xsimp_start
  repeat xsimp_step_l
  repeat' xsimp_step_r
  sorry
  sorry

#try xsimpl_demo_rhs_hexists {H1 H2 H3 H4 p}:
  H1 ==> H2 ** \∃ (n: Nat), (p ~~> n ** H3) ** H4
:= by
  xsimp_start
  repeat xsimp_step_l
  repeat' xsimp_step_r
  sorry

#try {H1 H2 H3 H4} {p}:
  H1 ** (p ~~> 3) ==> H2 ** \∃ (n: Nat), (p ~~> n ** H3) ** H4
:= by
  xsimp_start
  repeat xsimp_step_l
  repeat' xsimp_step_r
  sorry

#try {H1 H2 H4} {p}:
  H1 ** (p ~~> 3) ==> H2 ** \∃ (n: Nat), (p ~~> n ** \[n > 0]) ** H4
:= by
  xsimp_start
  repeat xsimp_step_l
  repeat' xsimp_step_r
  sorry
end Examples
