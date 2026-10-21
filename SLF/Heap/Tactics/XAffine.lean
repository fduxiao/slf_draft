import Qq
import SLF.Heap.Heap


namespace SLF.Heap.Tactics

open Lean Meta Elab Tactic Qq


elab "xaffine_core" : tactic => withMainContext do
  let goal: Q(Prop) ← getMainTarget
  match goal with
  | ~q(HProp.affine $H) =>
    evalTactic <| ← match H with
    | ~q(\[]) => `(tactic| apply HProp.affine_empty)
    | ~q(\[$P]) => `(tactic| apply HProp.affine_pure)
    | ~q($A ** $B) => `(tactic| apply HProp.affine_star)
    | ~q(HProp.exists $J) => `(tactic| apply HProp.affine_exists)
    | ~q(HProp.forall $J) => `(tactic| apply HProp.affine_forall)
    | ~q(HProp.gc) => `(tactic| apply HProp.affine_gc)
    | _ => throwError "xaffine_core tactic only works on goals of the form C ===> D"
  | _ => throwError "xaffine_core tactic only works on goals of the form C ===> D"
