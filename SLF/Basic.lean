import SLF.WP

namespace Basic
open SLF Lang WP Heap XSimp

def incr : Val := [slf|
  vfun p =>
    let n := !p in
    let m := n + 1 in
    p := m
]

theorem incr_triple : ∀ (p: Loc) (n: Int),
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

theorem example_let_triple : ∀ (n: Int),
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

theorem quadruple_triple : ∀ (n: Int),
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

theorem inplace_double_triple : ∀ (p: Loc) (n: Int),
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

theorem incr_two_triple : ∀ (p q: Loc) (n m: Int),
  Triple [slf| [incr_two] [p] [q] ]
    (p ~~> n ** q ~~> m) (fun _ => p ~~> ↑(n + 1) ** q ~~> ↑(m + 1))
:= by
  intro p q n m
  xwp
  xapp incr_triple
  xapp incr_triple
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
  xapp incr_triple
  xapp incr_triple
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
  xapp incr_triple

theorem triple_incr_first (p q: Loc) (n: Int):
  Triple [slf| [incr_first] [p] [q] ]
    (p ~~> n)
    (fun _ => p ~~> ↑(n + 1))
:= by
  xwp
  xapp incr_triple

example (p q: Loc) (n m: Int):
  Triple [slf| [incr_first] [p] [q] ]
    (p ~~> n ** q ~~> m)
    (fun _ => p ~~> ↑(n + 1) ** q ~~> m)
:= by
  xwp'
  xapp triple_incr_first
