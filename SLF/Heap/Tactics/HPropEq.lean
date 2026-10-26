import SLF.Heap.Heap

namespace SLF.Heap
open Map

section Instances
/-!
## `ac_rfl` of `**`
-/
instance : Std.Antisymm (· ==> ·) where
  antisymm := @HProp.imp_antisym

instance : Std.Refl (· ==> ·) where
  refl := @HProp.imp_refl

instance : Std.Commutative (· ** ·) where
  comm := @HProp.star_comm

instance : Std.Associative (· ** ·) where
  assoc := @HProp.star_assoc

example {H1 H2 H3 H4}:
  H1 ** H2 ** H3 ** H4 = (H1 ** H4) ** (H2 ** H3)
:= by
  ac_rfl

end Instances

section TacticHPropEq

open Lean.Parser.Tactic
/--
`hprop_eq` is a tactic that first simplifies all occurrences of `\[]` in `**` expressions,
and then applies `ac_rfl` to decide equality of `star` expressions.
-/
scoped syntax "hprop_eq" (" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? : tactic

scoped macro_rules
  | `(tactic| hprop_eq only $[ [$[$x:term],* ] ]?) =>
    `(tactic| (try simp only $[ [ $[$x:term],* ] ]?) <;> first | rfl /-| ac_rfl -/| grind)
  | `(tactic| hprop_eq $[ [$[$x:term],* ] ]?) =>
    `(tactic| (try simp $[ [ $[$x:term],* ] ]?) <;> first | rfl /-| ac_rfl -/| grind)

/-!
`ac_rfl` will cause some trouble (at least in v4.35.0). See the following examples.
-/
example (f: Nat → Nat):
  f 2 = 2 →
  (forall {m n: Nat}, m = n → n = 6 → m = 6 ) →
  ∃ k, 3 * (f (k + 1)) = 6
:= by
  intro E H
  apply Exists.intro ?k
  . apply H
    . show 3 * (f (?k + 1)) = (f (?k + 1)) * 3
      lia
    . show f (1 + 1) * 3 = 6
      simp_all

#try (f: Nat → Nat):
  f 2 = 2 →
  (forall {m n: Nat}, m = n → n = 6 → m = 6 ) →
  ∃ k, 3 * (f (k + 1)) = 6
:= by
  intro E H
  apply Exists.intro ?k
  . apply H
    . show 3 * (f (?k + 1)) = (f (?k + 1)) * 3
      ac_rfl
    . -- f (0 + 1) * 3 = 6
      sorry

end TacticHPropEq

section Examples
/-!
The following are some examples from SLF.
-/

example {H1 H2 H3}:
  (H2 ** H1 -* H3) ** \[] = (H1 ** H2 -* H3) ** \[]
:= by
  hprop_eq

example (H1 H2): H1 ** H2 ** \[] = H2 ** H1 ** \[] ** \[] := by
  hprop_eq

example (H1 H2 H3 H4):
  H1 ** H2 ** \[] ** H3 ** H4 ** \[] = H4 ** H3 ** H2 ** H1 ** \[]
:= by
  hprop_eq

example {H1 H2 H3 H}:
  H1 ** H2 ** H3 ** H = H3 ** H1 ** H2 ** H
:= by
  hprop_eq

example {H1 H2 H3 H4 H5 H6 H7 H8 H}:
  H1 ** H2 ** H3 ** H4 ** H5 ** H6 ** H7 ** H8 ** H
  = H8 ** H1 ** H2 ** H3 ** H4 ** H5 ** H6 ** H7 ** H
:= by
  hprop_eq
end Examples
