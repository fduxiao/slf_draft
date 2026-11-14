import SLF.WP

namespace Basic
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

def example_let : Val := [slf|
  vfun n =>
    let a := n + 1 in
    let b := n - 1 in
    a + b
]

theorem triple_example_let : ∀ (n: Int),
  Triple (.app example_let n) \[] (fun r => \[r = ↑(2 * n)])
:=by
  intro n
  xwp
  xstep
  xstep
  xstep
  xsimp
  omega

def quadruple : Val := [slf|
  vfun n =>
    let m := n + n in
    m + m
]

theorem triple_quadruple : ∀ (n: Int),
  Triple (.app quadruple n) \[] (fun r => \[r = ↑(4 * n)])
:=by
  intro n
  xwp
  xstep
  xstep
  xsimp
  omega

def inplace_double : Val := [slf|
  vfun p =>
    let n := !p in
    let m := n + n in
    p := m
]

theorem triple_inplace_double : ∀ (p: Loc) (n: Int),
  Triple (.app inplace_double p) (p ~~> n) (fun _ => p ~~> ↑(2 * n))
:=by
  intro p n
  xwp
  xstep
  xstep
  xstep
  xsimp
  omega

def incr_two: Val := [slf|
  vfun p q =>
    [incr] p;
    [incr] q
]

theorem triple_incr_two : ∀ (p q: Loc) (n m: Int),
  Triple [slf| [incr_two] [p] [q] ]
    (p ~~> n ** q ~~> m) (fun _ => p ~~> ↑(n + 1) ** q ~~> ↑(m + 1))
:= by
  intro p q n m
  xwp
  xapp triple_incr
  xapp triple_incr
  xsimp

def aliased_call : Val := [slf|
  vfun p =>
    [incr_two] p p
]

theorem triple_incr_two_aliased : ∀ (p: Loc) (n: Int),
  Triple [slf| [incr_two] [p] [p]]
    (p ~~> n)
    (fun _ => p ~~> ↑(n + 2))
:= by
  intro p n
  xwp
  xapp triple_incr
  xapp triple_incr
  xsimp
  lia

theorem triple_aliased_call : ∀ (p: Loc) (n: Int),
  Triple (.app aliased_call p)
    (p ~~> n)
    (fun _ => p ~~> ↑(n + 2))
:= by
  intro p n
  xwp
  xapp triple_incr_two_aliased

def incr_first : Val := [slf|
  vfun p q =>
    [incr] p
]

example (p q: Loc) (n m: Int):
  Triple [slf| [incr_first] [p] [q] ]
    (p ~~> n ** q ~~> m)
    (fun _ => p ~~> ↑(n + 1) ** q ~~> m)
:= by
  xwp
  xapp triple_incr

theorem triple_incr_first (p q: Loc) (n: Int):
  Triple [slf| [incr_first] [p] [q] ]
    (p ~~> n)
    (fun _ => p ~~> ↑(n + 1))
:= by
  xwp
  xapp triple_incr

example (p q: Loc) (n m: Int):
  Triple [slf| [incr_first] [p] [q] ]
    (p ~~> n ** q ~~> m)
    (fun _ => p ~~> ↑(n + 1) ** q ~~> m)
:= by
  xwp'
  xapp triple_incr_first


def transfer : Val := [slf|
  vfun p q =>
    let n := !p in
    let m := !q in
    let s := n + m in
    p := s;
    q := 0
]

theorem triple_transfer : ∀ (p q: Loc) (n m: Int),
  Triple [slf| [transfer] [p] [q]] (p ~~> n ** q ~~> m) (fun _ => p ~~> ↑(n + m) ** q ~~> 0)
:= by
  intro p q n m
  xwp
  xsteps
  xsimp

def ref_greater : Val := [slf|
  vfun p =>
    let n := !p in
    let m := n + 1 in
    ref m
]

theorem triple_ref_greater : ∀ (p: Loc) (n: Int),
  Triple (.app ref_greater p) (p ~~> n) (fun r => p ~~> n ** \∃ q: Loc, \[r == q] ** q ~~> ↑(n + 1))
:= by
  intro p n
  xwp
  xstep
  xstep
  xref q
  xsimp [q]

example : ∀ (p: Loc) (n: Int),
  Triple (.app ref_greater p) (p ~~> n) (funloc q => p ~~> n ** q ~~> ↑(n + 1))
:= by
  intro p n
  xwp
  xstep
  xstep
  xref q
  xsimp [q]

example :
  Triple [slf| ref 0; ref 1] \[] (funloc p q => p ~~> 1 ** q ~~> 0)
:= by
  xwp
  xref q
  xref p
  xsimp [p, q]

def succ_using_incr_attempt: Val := [slf|
  vfun n =>
    let p := ref n in
    [incr] p;
    ! p
]

#try : ∀ (n: Int),
  Triple [slf| [succ_using_incr_attempt] [n]] \[] (fun r => \[r = ↑(n + 1)])
:= by
  intro n
  xwp
  xref p
  xapp triple_incr
  xstep
  sorry

example : ∀ (n: Int),
  Triple [slf| [succ_using_incr_attempt] [n]]
    \[]
    (fun r => \[r = ↑(n + 1)] ** \∃ p, p ~~> ↑(n + 1))
:= by
  intro n
  xwp
  xref p
  xapp triple_incr
  xstep
  xsimp

def succ_using_incr: Val := [slf|
  vfun n =>
    let p := ref n in
    [incr] p;
    let x := !p in
    free p;
    x
]

theorem triple_succ_using_incr : ∀ n: Int,
  Triple (.app succ_using_incr n)
    \[]
    (fun r => \[r = ↑(n + 1)])
:= by
  intro n
  xwp
  xref p
  xsteps
  xapp triple_incr
  xsteps
  xsimp

def get_and_free : Val := [slf|
  vfun p =>
    let x := !p in
    free p;
    x
]

theorem triple_get_and_free : ∀ (p: Loc) (v: Val),
  Triple (.app get_and_free p)
    (p ~~> v)
    (fun r => \[r = v])
:= by
  intro p v
  xwp
  xsteps
  xsimp
