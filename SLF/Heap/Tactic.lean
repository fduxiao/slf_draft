import Qq
import SLF.Heap.Heap
import SLF.Heap.Tactics.HPropEq
import SLF.Heap.Tactics.XSimpDef
import SLF.Heap.Tactics.XSimpLStep
import SLF.Heap.Tactics.XSimpRStep
import SLF.Heap.Tactics.XSimp

/-!
# How does the xsimp tactic work?
Our goal is to prove some `H1 ** H2 ** ... ==> H1' ** H2' ** ...`.
Note that this `**` is associative and commutative.

We have the following rules to simplify such goals.
- `\[P] ** H ==> H'` is simplified to `P → H ==> H'`;
- `\∃ (x: T), H ==> H'` is simplified to `∀ (x: T), H ==> H'`;
- `H1 ** (H1 -* H2) ==> H3` is simplified to `H2 ==> H3`;
- `H1 ** H2 ==> H1 ** H3` is simplified to `H2 ==> H3`;
- We can also simplify the `\∃` on the right by specifying the witness:
  `H1 ** H2 ==> \∃ x, \[x > 3]` --[x := 6]--> `H1 ** H2 ==> 6 > 3`;
- ...

In order to apply those rules, we break the left side into 3 parts `Hla`, `Hlw`, `Hlt`:
- `Hla`: the parts to be handled;
- `Hlw`: the wands;
- `Hlt`: the parts cannot be simplified by the above rules.

Given `H3 ** H1 ** H4 ** (H1 -* H2)` on the left side, we first break in
into a list `[H3, H1, H4, (H1 -* H2)]`, and set up the following initial state:
- `Hla := []`
- `Hlw := []`
-- `Hlt := [H3, H1, H4, H1 -* H2]`

At each simplification step, we try to move elements from `Hlt` to `Hla` or `Hlw`
according to the simplification rules.
- We look at `Hlt`. The first element is `H3`. We move it to `Hla` and get
  - `Hla := [H3]`
  - `Hlw := []`
  - `Hlt := [H1, H4, H1 -* H2]`
- Next, the first element of `Hlt` is `H1`. We move it to `Hla` and get
  - `Hla := [H1, H3]`
  - `Hlw := []`
  - `Hlt := [H4, H1 -* H2]`
- Next, the first element of `Hlt` is `H4`. We move it to `Hla` and get
  - `Hla := [H4, H1, H3]`
  - `Hlw := []`
  - `Hlt := [H1 -* H2]`
- Then, the first in `Hlt` is `H1 -* H2`. We move it to `Hlw` and get
  - `Hla := [H4, H1, H3]`
  - `Hlw := [H1 -* H2]`
  - `Hlt := []`
- Now `Hlt` is empty, and we look at `Hlw`. The first element is `H1 -* H2`.
  We compare `H1` with those in `Hla`. Since `H1` is present in `Hla`,
  we pull it out and move `H2` (those after `-*`) and `Hla` (in case new
  simplifications are possible) to `Hlt`.
  - `Hla := [H4, H3]`
  - `Hlw := []`
  - `Hlt := [H4, H3, H2]`
- ...

Similarly, we do the same for the right side of the goal.

To make the tactic, we first turn the HProp implication into an `XSimp`:
```lean
def XSimp: (HProp × HProp × HProp) → (HProp × HProp × HProp) → Prop
  | (Hla, Hlw, Hlt), (Hra, Hrg, Hrt) => Hla ** (Hlw ** Hlt) ==> (Hra ** (Hrg ** Hrt))
```
At each step, we just compare the arguments of `XSimp` on the left and right sides
and apply the simplification rules accordingly. We also have the following considerations:
- For the `\[P]` or `\∃` on the left, we always `intro` the corresponding variable or
  hypothesis into the context before we move on.
- For the `\∃` on the right, we put a list of _hints_.
Thus, the `xsimp` tactic do the following:
- put hints into the context;
- make a `TacticMark` to indicate those local declarations introduced during `xsimp`;
- turn the target into an `XSimp` expression;
- apply the simplification rules step by step;
- revert those local declarations introduced during `xsimp`;
- clear remaining hints;
- clear the `TacticMark`.

See the following examples.
-/

section Examples
open SLF Heap XSimp

#try {H1 H2 H3 H4 H}:
  H3 ** H1 ** H4 ** (H1 -* H2) ==> H
:= by
  -- `xsimp` plays the following:
  xsimp_start
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  repeat' xsimp_step
  simp
  clear_mark
  sorry

/-!
This shows how revert works.
-/
#try {H1 H2}:
  H1 ** \[3 = 4] ==> H2
:= by
  -- `xsimp` plays the following:
  xsimp_start
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  simp
  revert_after_mark
  clear_mark
  sorry

/-!
This shows how hints work
-/
#try {H1 H2}:
  H1 ==> \∃ x: Nat, \[x = 4] ** H2
:= by
  -- `xsimp [4]` plays the following:
  xsimp_hint_put 4
  xsimp_start
  xsimp_step
  guard_hyp xsimp_hint := xhint[4]
  guard_target = XSimp (H1 ** \[], \[], \[]) (\[], \[], (\∃ x, \[x = 4] ** H2) ** \[])
  -- we will instantiate the existential with the hint `4`
  xsimp_step
  guard_target = XSimp (H1 ** \[], \[], \[]) (\[], \[], (\[4 = 4] ** H2) ** \[])
  xsimp_step
  xsimp_step
  . guard_target = 4 = 4
    sorry
  . guard_target = XSimp (H1 ** \[], \[], \[]) (\[], \[], H2 ** \[])
    sorry

end Examples
