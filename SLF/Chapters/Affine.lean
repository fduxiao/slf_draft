import SLF.WP

namespace SLF.Chapters.Affine
open SLF Lang WP Heap XSimp

def incr : Val := [slf|
  vfun p =>
    let n := !p in
    let m := n + 1 in
    p := m
]

theorem triple_incr : ∀ (p: Loc) (n: Int),
  Triple (.app incr p) (p ~~> n) (fun _ => p ~~> ↑(n + 1))
:=by
  intro p n
  xwp
  xstep
  xstep
  xstep

def succ_using_incr: Val := [slf|
  vfun n =>
    let p := ref n in
    [incr] p;
    ! p
]

#try : ∀ (n: Int),
  Triple [slf| [succ_using_incr] [n]] \[] (fun r => \[r = ↑(n + 1)])
:= by
  intro n
  xwp
  xref p
  xapp triple_incr
  xstruct
  apply XLemmas.xapp_protect
  apply Triple.get (v := ↑(n + 1))
  xsimp_start
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step_lr
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  simp_all
  guard_target =
    p ~~> ↑(n + 1) ==> Protect (fun r => \[r = Val.int (n + 1)]) ↑(n + 1)
  simp only [Protect]
  guard_target =
    p ~~> ↑(n + 1) ==> \[True]
  simp
  sorry

theorem triple_succ_using_incr : ∀ (n: Int),
  Triple [slf| [succ_using_incr] [n]]
    \[]
    (fun r => \[r = ↑(n + 1)] ** \∃ p, p ~~> ↑(n + 1))
:= by
  intro n
  xwp
  xref p
  xapp triple_incr
  xstep
  xsimp

axiom triple_any_post : ∀ t H H' Q,
  Triple t H (Q *+ H') →
  Triple t H Q

macro "xref'" t:term : tactic => `(tactic|
  xapp_op <;> intro x $t E <;> subst x
)

example : ∀ (n: Int),
  Triple [slf| [succ_using_incr] [n]] \[] (fun r => \[r = ↑(n + 1)])
:= by
  intro n
  apply triple_any_post
  apply triple_succ_using_incr

example : ∀ (n: Int),
  Triple [slf| [succ_using_incr] [n]] \[] (fun r => \[r = ↑(n + 1)])
:= by
  intro n
  apply triple_any_post (H' := \GC)
  xwp
  xref p
  xapp triple_incr
  xstep

example : ∀ (n: Int),
  Triple [slf| [succ_using_incr] [n]] \[] (fun r => \[r = ↑(n + 1)])
:= by
  intro n
  apply triple_any_post (H' := \Top) -- here `\GC` is equivalent to `\Top`
  xwp
  xref p
  xapp triple_incr
  xstruct
  apply XLemmas.xapp_protect
  apply Triple.get (v := ↑(n + 1))
  xsimp_start
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step_lr
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  simp_all
  guard_target =
    -- compare with `p ~~> ↑(n + 1) ==> Protect (fun r => \[r = Val.int (n + 1)]) ↑(n + 1)`
    p ~~> ↑(n + 1) ==> Protect ((fun r => \[r = Val.int (n + 1)]) *+ \Top) ↑(n + 1)
  simp only [Protect]
  simp only [HProp.qstar]
  guard_target =
    -- compare with `p ~~> ↑(n + 1) ==> \[True]`
    p ~~> ↑(n + 1) ==> \[True] ** \Top
  simp
