import SLF.WP.WP

namespace SLF
open Map Lang Heap XSimp
/-!
`WP` is the semantic function for weakest preconditions. We hope to
define a `wpgen` function based on the syntactic structure of terms.
-/
namespace MSubst

@[grind]
abbrev Context := List (Var × Val)

@[grind]
def Context.lookup (v : Var) (ctx : Context) : Option Val := List.lookup v ctx

@[grind]
def Context.remove (v : Var) (ctx : Context) : Context := List.filter (fun p => p.1 != v) ctx

@[grind]
def Context.disjoint (ctx1 ctx2 : Context) : Prop :=
  ∀ x, (Context.lookup x ctx1) ≠ none → (Context.lookup x ctx2) = none

@[symm]
theorem Context.disjoint_symm {ctx1 ctx2 : Context} :
  Context.disjoint ctx1 ctx2 → Context.disjoint ctx2 ctx1
:= by
  grind

@[simp, grind]
def Context.equiv (ctx1 ctx2 : Context) : Prop :=
  ∀ v, Context.lookup v ctx1 = Context.lookup v ctx2

@[grind]
instance: HasEquiv Context where
  Equiv := Context.equiv

@[simp, refl, grind =]
theorem Context.equiv_refl {ctx : Context} :
  ctx ≈ ctx
:= by
  intro v
  grind

-- This line has to be long enough in order to trigger the error.

@[simp, symm, grind .]
theorem Context.equiv_symm {ctx1 ctx2 : Context} :
  ctx1 ≈ ctx2 → ctx2 ≈ ctx1
:= by
  simp
  grind

@[simp, grind =]
theorem Context.lookup_cons {x : Var} {ctx: Context} {y : Var} {v : Val}:
  Context.lookup x ((y, v) :: ctx) = (if x == y then some v else ctx.lookup x)
:= by
  induction ctx <;> grind

@[simp, grind =]
theorem Context.lookup_app {x : Var} {ctx1 ctx2 : Context} :
  (ctx1 ++ ctx2).lookup x = (ctx1.lookup x <|> ctx2.lookup x)
:= by
  induction ctx1 <;> grind

@[simp]
theorem Context.lookup_remove {x y : Var} {ctx : Context}:
  (ctx.remove y).lookup x = if x == y then none else ctx.lookup x
:= by
  induction ctx <;> grind

@[simp, grind =]
theorem Context.cons_remove_eq {x v} {ctx : Context}:
  (x, v) :: ctx ≈ (x, v) :: Context.remove x ctx
:= by
  intro y
  simp
  grind

@[simp]
theorem Context.remove_app {x : Var} {ctx1 ctx2 : Context} :
  (ctx1 ++ ctx2).remove x = ctx1.remove x ++ ctx2.remove x
:= by
  induction ctx1 <;> grind

@[simp]
theorem Context.remove_equiv {x : Var} {ctx1 ctx2 : Context} :
  ctx1 ≈ ctx2 → ctx1.remove x ≈ ctx2.remove x
:= by
  simp [Context.equiv]
  intro E v
  simp [E]

@[simp]
theorem Context.remove_disjoint {x : Var} {ctx1 ctx2 : Context} :
  Context.disjoint ctx1 ctx2 → Context.disjoint (ctx1.remove x) (ctx2.remove x)
:= by
  intro D v H
  cases E: (ctx2.remove x).lookup v with
  | none => simp
  | some _ =>
    unfold Context.disjoint at D
    simp_all

@[simp, grind =]
theorem Context.disjoint_equiv_app {ctx1 ctx2: Context} :
  Context.disjoint ctx1 ctx2 → (ctx1 ++ ctx2) ≈ (ctx2 ++ ctx1)
:= by
  simp [disjoint]
  grind

end MSubst

open MSubst

section MSubst

@[grind]
def Lang.Term.isubst (ctx : Context) (t: Term): Term :=
  match t with
  | .val v => v
  | .var x =>
    match ctx.lookup x with
    | some v => v
    | none => t
  | .fun x t1 =>
       .fun x (isubst (ctx.remove x) t1)
  | .fix f x t1 =>
       .fix f x (isubst ((ctx.remove f).remove x) t1)
  | .if t0 t1 t2 =>
       .if (isubst ctx t0) (isubst ctx t1) (isubst ctx t2)
  | .seq t1 t2 =>
       .seq (isubst ctx t1) (isubst ctx t2)
  | .let x t1 t2 =>
       .let x (isubst ctx t1) (isubst (ctx.remove x) t2)
  | .app t1 t2 =>
       .app (isubst ctx t1) (isubst ctx t2)

@[simp, grind =]
theorem Lang.Term.isubst_nil {t: Term}:
  t.isubst [] = t
:= by
  induction t using Term.ind <;> grind

@[grind .]
theorem Lang.Term.isubst_cons {t: Term} {ctx: Context} {x: Var} {v: Val}:
  t.isubst ((x, v) :: ctx) = (t.subst x v).isubst ctx
:= by
  induction t using Term.ind generalizing ctx <;> try grind

@[simp, grind =]
theorem Lang.Term.isubst_single {t: Term} {x: Var} {v: Val}:
  t.isubst [(x, v)] = t.subst x v
:= by
  induction t using Term.ind <;> grind

@[grind .]
theorem Lang.Term.isubst_ctx_eq {t: Term} {ctx1 ctx2: Context}:
  ctx1 ≈ ctx2 → t.isubst ctx1 = t.isubst ctx2
:= by
  intro E
  induction t using Term.ind generalizing ctx1 ctx2 <;> try grind
  case var x =>
    simp_all
    grind
  case «fun» x t IH =>
    simp only [Lang.Term.isubst]
    solve_by_elim [Context.remove_equiv]
  case fix f x t IH =>
    simp only [Lang.Term.isubst]
    solve_by_elim [Context.remove_equiv]
  case «let» x t1 t2 IH1 IH2 =>
    simp only [Lang.Term.isubst]
    simp
    and_intros
    . apply IH1 E
    . apply IH2 (Context.remove_equiv E)

@[grind =]
theorem Lang.Term.isubst_app {t: Term} {ctx1 ctx2: Context}:
  t.isubst (ctx1 ++ ctx2) = (t.isubst ctx1).isubst ctx2
:= by
  induction t using Term.ind generalizing ctx1 ctx2 <;> try grind

@[grind =]
theorem Lang.Term.isubst_app_swap {t: Term} {ctx1 ctx2: Context}:
  ctx1.disjoint ctx2 →
  t.isubst (ctx1 ++ ctx2) = t.isubst (ctx2 ++ ctx1)
:= by
  intro H
  apply Term.isubst_ctx_eq
  apply Context.disjoint_equiv_app
  exact H

@[grind =]
theorem Lang.Term.isubst_remove {t: Term} {ctx: Context} {x v}:
  t.isubst ((x, v) :: ctx) = (t.isubst (ctx.remove x)).subst x v
:= by
  rw [←Term.isubst_single]
  rw [←Term.isubst_app]
  rw [Term.isubst_app_swap]
  . apply Term.isubst_ctx_eq
    apply Context.cons_remove_eq
  . grind

@[grind =]
theorem Lang.Term.isubst_remove2 {t: Term} {ctx: Context} {f vf x vx}:
  t.isubst ((f, vf) :: (x, vx) :: ctx) = ((t.isubst <| (ctx.remove f).remove x).subst f vf).subst x vx
:= by
  repeat rw [←Term.isubst_single]
  repeat rw [←Term.isubst_app]
  rw [Term.isubst_app_swap]
  . apply Term.isubst_ctx_eq
    intro y
    simp
    grind
  . grind

end MSubst

section MKStruct

/--
`Formula: (Val → HProp) → HProp` is intended to be a function that
`F Q` is the weakest precondition.
-/
abbrev Formula := (Val → HProp) → HProp

@[grind]
def mkStruct (F: Formula): Formula :=
  fun Q => \∃ Q', F Q' ** (Q' -** Q)

@[simp, grind .]
theorem mkStruct.ramified {Q1 Q2 F}:
  (mkStruct F Q1) ** (Q1 -** Q2) ==> (mkStruct F Q2)
:= by
  unfold mkStruct
  xsimp

@[simp, grind .]
theorem mkStruct.erase {Q F}:
  F Q ==> mkStruct F Q
:= by
  unfold mkStruct
  xsimp

@[simp, grind =]
theorem mkStruct.eq_wp {t: Term}:
  mkStruct (WP t) = WP t
:= by
  funext Q
  ext
  . simp [mkStruct]
    intro Q'
    apply WP.ramified
  . apply mkStruct.erase

@[grind .]
theorem mkStruct.conseq {F Q1 Q2}:
  Q1 ===> Q2 →
  mkStruct F Q1 ==> mkStruct F Q2
:= by
  intro H
  unfold mkStruct
  xpull
  intros Q'
  xsimp [Q']
  xchange H
  simp

@[simp, grind .]
theorem mkStruct.frame {F H Q}:
  (mkStruct F Q) ** H ==> mkStruct F (Q *+ H)
:= by
  unfold mkStruct
  xpull
  intro Q'
  xsimp [Q']
  grind

@[grind .]
theorem mkStruct.monotone {F1 F2 Q}:
  (∀ Q, F1 Q ==> F2 Q) →
  mkStruct F1 Q ==> mkStruct F2 Q
:= by
  intro H
  unfold mkStruct
  xpull
  intro Q'
  xchange H
  xsimp [Q']

end MKStruct

section WPGen

@[grind]
def wpgen.fail: Formula := fun _ => \[False]
@[grind]
def wpgen.val (v: Val): Formula := fun Q => Q v
@[grind]
def wpgen.fun (Fof: Val → Formula): Formula := fun Q =>
  \∀ vf: Val, \[∀ vx Q', Fof vx Q' ==> WP (.app vf vx) Q'] -* Q vf
@[grind]
def wpgen.fix (Fof: Val → Val → Formula) : Formula := fun Q =>
  \∀ vf: Val, \[∀ vx Q', Fof vf vx Q' ==> WP (.app vf vx) Q'] -* Q vf
@[grind]
def wpgen.var (ctx: MSubst.Context) (x: Var) : Formula :=
  match ctx.lookup x with
  | none => wpgen.fail
  | some v => wpgen.val v
@[grind]
def wpgen.seq (F1 F2: Formula) : Formula := fun Q =>
  F1 (fun _ => F2 Q)
@[grind]
def wpgen.let (F1: Formula) (F2of: Val → Formula) : Formula := fun Q =>
  F1 (fun v => F2of v Q)
@[grind]
def wpgen.if (t: Term) (F1 F2: Formula) : Formula := fun Q =>
  \∃ (b: Bool), \[t = b] ** (if b then F1 Q else F2 Q)
@[grind]
def wpgen.if_term (F0 F1 F2: Formula) : Formula :=
  wpgen.let F0 (fun v => mkStruct (wpgen.if v F1 F2))
@[grind]
def wpgen.app (t: Term) : Formula := fun Q =>
  \∃ H, H ** \[Triple t H Q]

def wpgen (ctx: Context) (t: Term) : Formula :=
  mkStruct <| match t with
    | .val v => wpgen.val v
    | .var x => wpgen.var ctx x
    | .fun x t1 => wpgen.fun (fun v => wpgen ((x, v)::ctx) t1)
    | .fix f x t1 => wpgen.fix (fun vf v => wpgen ((f, vf)::(x, v)::ctx) t1)
    | .if t0 t1 t2 => wpgen.if (t0.isubst ctx) (wpgen ctx t1) (wpgen ctx t2)
    | .seq t1 t2 => wpgen.seq (wpgen ctx t1) (wpgen ctx t2)
    | .let x t1 t2 => wpgen.let (wpgen ctx t1) (fun v => wpgen ((x, v)::ctx) t2)
    | .app _ _ => wpgen.app (t.isubst ctx)

end WPGen

section SoundnessOfWPGen

/--
`sound t F` is defined to be `∀ Q, F Q ==> WP t Q`, i.e., `F Q` is the weakest precondition.
-/
@[grind]
def Formula.sound (t: Term) (F: Formula) : Prop := ∀ Q, F Q ==> WP t Q

@[simp, grind .]
theorem WP.sound (t: Term):
  Formula.sound t (WP t)
:= by
  intro Q
  simp

@[simp, grind .]
theorem mkStruct.sound {t} {F: Formula}:
  F.sound t →
  (mkStruct F).sound t
:= by
  intro M
  unfold Formula.sound
  intro Q
  rw [← mkStruct.eq_wp]
  apply mkStruct.monotone
  exact M

@[simp, grind .]
theorem wpgen.fail_sound {t: Term}:
  Formula.sound t wpgen.fail
:= by
  intro Q
  simp [wpgen.fail]
  grind

@[simp, grind .]
theorem wpgen.val_sound {v: Val}:
  Formula.sound v (wpgen.val v)
:= by
  intro Q
  simp [wpgen.val]
  apply WP.val

@[grind .]
theorem wpgen.fun_sound {x} {t1: Term} {Fof}:
  (∀ vx, Formula.sound (t1.subst x vx) (Fof vx)) →
  Formula.sound (.fun x t1) (wpgen.fun Fof)
:= by
  intro M
  intro Q
  unfold wpgen.fun
  refine HProp.forall_left (x := Val.fun x t1) ?_
  -- apply xchange_rewrite (Q := WP (Term.fun x t1) Q) (motive := fun x => x) (by hprop_eq) (HProp.imp_mp (HProp.wand_pure_left _)) (by grind)
  xchange HProp.wand_pure_left
  . exact WP.fun
  . intro vx Q'
    specialize M vx
    unfold Formula.sound at M
    xchange M
    apply WP.app_fun
    rfl

@[grind .]
theorem wpgen.fix_sound {f x} {t1: Term} {Fof}:
  (∀ vf vx, Formula.sound (t1.subst f vf |>.subst x vx) (Fof vf vx)) →
  Formula.sound (.fix f x t1) (wpgen.fix Fof)
:= by
  intro M
  intro Q
  unfold wpgen.fix
  refine HProp.forall_left (x := Val.fix f x t1) ?_
  xchange HProp.wand_pure_left
  . exact WP.fix
  . intro vx Q'
    -- `vf` is the fixed-point value for the function `f`
    specialize M (Val.fix f x t1) vx
    unfold Formula.sound at M
    xchange M
    apply WP.app_fix
    rfl

@[grind .]
theorem wpgen.seq_sound {F1 F2 t1 t2}:
  Formula.sound t1 F1 →
  Formula.sound t2 F2 →
  Formula.sound (.seq t1 t2) (wpgen.seq F1 F2)
:= by
  intro S1 S2 Q
  apply WP.seq.trans_r
  unfold wpgen.seq
  unfold Formula.sound at *
  xchange S1
  apply WP.conseq
  xchange S2
  simp

@[grind .]
theorem wpgen.let_sound {F1 F2of x t1 t2}:
  Formula.sound t1 F1 →
  (∀ v, Formula.sound (.subst x v t2) (F2of v)) →
  Formula.sound (.let x t1 t2) (wpgen.let F1 F2of)
:= by
  intro S1 S2 Q
  apply WP.let.trans_r
  unfold wpgen.let
  xchange S1 _
  apply WP.conseq
  xchange S2 _ _
  simp

@[grind .]
theorem wpgen.if_sound {F1 F2 t0 t1 t2}:
  Formula.sound t1 F1 →
  Formula.sound t2 F2 →
  Formula.sound (.if t0 t1 t2) (wpgen.if t0 F1 F2)
:= by
  intro S1 S2 Q
  unfold wpgen.if
  xpull
  intro b HB
  cases HB
  apply WP.if.trans_r
  split
  . apply S1
  . apply S2

@[grind .]
theorem wpgen.app_sound {t}:
  Formula.sound t (wpgen.app t)
:= by
  intro Q
  unfold wpgen.app
  xsimp
  intro H HT
  apply WP.equiv.mpr
  exact HT

@[simp, grind .]
theorem wpgen.sound {ctx t}:
  Formula.sound (t.isubst ctx) (wpgen ctx t)
:= by
  induction t using Term.ind generalizing ctx <;> apply mkStruct.sound
  case «fun» x t IH =>
    apply wpgen.fun_sound
    grind
  case fix f x t IH =>
    apply wpgen.fix_sound
    grind
  case «let» x t1 t2 IH1 IH2 =>
    apply wpgen.let_sound
    . grind
    . grind
  all_goals grind

@[simp, grind .]
theorem wpgen.nil_sound {t Q}:
  wpgen [] t Q ==> WP t Q
:= by
  let H := wpgen.sound (ctx := []) (t := t)
  simp at H
  apply H

@[grind .]
theorem Triple.of_wpgen {t H Q}:
  H ==> wpgen [] t Q →
  Triple t H Q
:= by
  intro M
  rw [← WP.equiv]
  xchange M
  apply wpgen.nil_sound

end SoundnessOfWPGen

namespace XLemmas

theorem xstruct {F H Q}:
  H ==> F Q →
  H ==> mkStruct F Q
:= by
  grind

theorem xval {v H Q}:
  H ==> Q v →
  H ==> wpgen.val v Q
:= by
  grind

theorem xlet {H F1 F2of Q}:
  H ==> F1 (fun v => F2of v Q) →
  H ==> wpgen.let F1 F2of Q
:= by
  intro M
  xchange M
  grind

theorem xseq {H F1 F2 Q}:
  H ==> F1 (fun _v => F2 Q) →
  H ==> wpgen.seq F1 F2 Q
:= by
  intro M
  xchange M
  grind

theorem xif {b H F1 F2 Q}:
  (b = true → H ==> F1 Q) →
  (b = false → H ==> F2 Q) →
  H ==> wpgen.if b F1 F2 Q
:= by
  intro M1 M2
  unfold wpgen.if
  xsimp [b]
  cases b <;> simp
  . apply M2
    rfl
  . apply M1
    rfl

theorem xif_true {H F1 F2 Q}:
  (H ==> F1 Q) →
  H ==> wpgen.if true F1 F2 Q
:= by
  intro H
  apply xif
  . simp_all
  . simp_all

theorem xif_false {H F1 F2 Q}:
  (H ==> F2 Q) →
  H ==> wpgen.if false F1 F2 Q
:= by
  intro H
  apply xif
  . simp_all
  . simp_all

theorem xapp_protect {t Q1 H1 H Q}:
  Triple t H1 Q1 →
  H ==> H1 ** (Q1 -** Protect Q) →
  H ==> wpgen.app t Q
:= by
  intro M W
  unfold wpgen.app
  xsimp
  grind

theorem xapp {t Q1 H1 H Q}:
  Triple t H1 Q1 →
  H ==> H1 ** (Q1 -** Q) →
  H ==> wpgen.app t Q
:= by
  intro M W
  unfold wpgen.app
  xsimp
  grind

theorem xfun_spec {S:Val → Prop} {H Q Fof}:
  (∀ vf: Val,
    (∀ (vx: Val) H' Q', (H' ==> Fof vx Q') → Triple (.app vf vx) H' Q') →
    S vf) →
  (∀ vf, S vf → (H ==> Q vf)) →
  H ==> wpgen.fun Fof Q
:= by
  intro M1 M2
  unfold wpgen.fun
  xsimp
  intro vf N
  apply M2
  apply M1
  intro _ _ _ K
  rw [← WP.equiv]
  xchange K
  apply N

theorem xfun_nospec {H Q Fof}:
  (∀ vf: Val,
    (∀ (vx: Val) H' Q', (H' ==> Fof vx Q') → Triple (.app vf vx) H' Q') →
    (H ==> Q vf)) →
  H ==> wpgen.fun Fof Q
:= by
  intro M
  unfold wpgen.fun
  xsimp
  intros vf N
  apply M
  intro _ _ _ K
  rw [← WP.equiv]
  xchange K
  apply N

theorem xfix_spec {S:Val → Prop} {H Q Fof}:
  (∀ vf: Val,
    (∀ (vx: Val) H' Q', (H' ==> Fof vf vx Q') → Triple (.app vf vx) H' Q') →
    S vf) →
  (∀ vf: Val, S vf → (H ==> Q vf)) →
  H ==> wpgen.fix Fof Q
:= by
  intro M1 M2
  unfold wpgen.fix
  xsimp
  intros vf N
  apply M2
  apply M1
  intro _ _ _ K
  rw [← WP.equiv]
  xchange K
  apply N

theorem xfix_nospec {H Q Fof}:
  (∀ vf: Val,
     (∀ (vx: Val) H' Q', (H' ==> Fof vf vx Q') → Triple (.app vf vx) H' Q') →
     (H ==> Q vf)) →
  H ==> wpgen.fix Fof Q
:= by
  intro M
  unfold wpgen.fix
  xsimp
  intros vf N
  apply M
  intro _ _ _ K
  rw [← WP.equiv]
  xchange K
  apply N

theorem xwp_fun {v1 v2 x t H Q}:
  v1 = Val.fun x t →
  H ==> wpgen [(x,v2)] t Q →
  Triple (.app v1 v2) H Q
:= by
  intro M1 M2
  rw [← WP.equiv]
  xchange M2
  xchange (wpgen.sound (ctx := [(x,v2)]) (t := t) Q)
  simp
  apply WP.app_fun
  exact M1

theorem xwp_fix {v1 v2 f x t H Q}:
  v1 = Val.fix f x t →
  f ≠ x →
  H ==> wpgen ([(f,v1),(x,v2)]) t Q →
  Triple (.app v1 v2) H Q
:= by
  intro M1 N M2
  rw [← WP.equiv]
  xchange M2
  xchange (wpgen.sound (ctx := [(f,v1),(x,v2)]) (t := t) Q)
  rw [Term.isubst_cons]
  rw [Term.isubst_single]
  apply WP.app_fix
  exact M1

theorem xtriple {t H} {Q: Val → HProp}:
  H ==> mkStruct (wpgen.app t) Q →
  Triple t H Q
:= by
  intro M
  rw [← WP.equiv]
  xchange M
  unfold mkStruct wpgen.app
  xpull
  intros Q' H' N
  rw [← WP.equiv] at N
  xchange N
  apply WP.ramified

example (p: Loc) (n: Int):
  let incr: Val := [slf|
    vfun p =>
      let n := !p in
      let m := n + 1 in
      p := m
  ]
  Triple (.app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n + 1: Int))
:= by
  apply xwp_fun rfl
  apply xstruct
  apply xlet
  apply xstruct
  apply xapp (Triple.get); xsimp
  apply xstruct
  apply xlet
  apply xstruct
  apply xapp (Triple.add); xsimp
  apply xstruct
  apply xapp (Triple.set)
  xsimp

end XLemmas

section Notations
open Lean Meta Elab Tactic Parser.Tactic PrettyPrinter Delaborator SubExpr Qq

-- First the notation for wpgen structures
declare_syntax_cat xwp_code (behavior := symbol)
syntax "[" term "]": xwp_code
syntax "(" xwp_code ")": xwp_code
syntax ppDedent("`(" xwp_code ")"): xwp_code
syntax "<[" xwp_code "]>": term
syntax "Fail": xwp_code
syntax "Val " term: xwp_code
syntax ppGroup("Let " ident " := " xwp_code " in ") ppDedent(ppLine xwp_code) : xwp_code
syntax ppGroup("Seq " xwp_code " ; ") ppDedent(ppLine xwp_code) : xwp_code
syntax "App " slf_term : xwp_code
syntax
  ppGroup("If " slf_term " Then ")
    ppGroup(ppLine xwp_code)
  ppDedent(ppLine " Else ")
    ppGroup(ppLine xwp_code) : xwp_code
syntax "Fun " ident " => " xwp_code : xwp_code
syntax "Fix " ident ident " => " xwp_code : xwp_code

macro_rules
  | `(<[ [$F] ]>) => `($F)
  | `(<[ ($F) ]>) => `(<[ $F ]>)
  | `(<[ `($F) ]>) => `(mkStruct <[ $F ]>)
  | `(<[ Fail ]>) => `(wpgen.fail)
  | `(<[ Val $v ]>) => `(wpgen.val $v)
  | `(<[ Let $x := $F1 in $F2 ]>) => `(wpgen.let <[ $F1 ]> (fun $x => <[ $F2 ]>))
  | `(<[ Seq $F1 ; $F2 ]>) => `(wpgen.seq <[ $F1 ]> <[ $F2 ]>)
  | `(<[ App $t ]>) => `(wpgen.app [slf| $t ])
  | `(<[ If $t Then $F1 Else $F2 ]>) => `(wpgen.if [slf| $t] <[ $F1 ]> <[ $F2 ]>)
  | `(<[ Fun $x => $F ]>) => `(wpgen.fun (fun $x => <[ $F ]>))
  | `(<[ Fix $f $x => $F ]>) => `(wpgen.fix (fun $f $x => <[ $F ]>))

def parseToXwp: TSyntax `term → UnexpandM (TSyntax `xwp_code)
  | `(<[$t]>) => `(xwp_code| $t)
  | `($t) => `(xwp_code| [$t])

def parseToSlf: TSyntax `term → UnexpandM (TSyntax `slf_term)
  | `([slf| $t]) => `(slf_term| $t)
  | `($t) => `(slf_term| [$t])

@[app_unexpander mkStruct]
def unexpandMkStruct : Lean.PrettyPrinter.Unexpander
  | `($_ <[ $F ]>) => `(<[ `($F) ]>)
  | `($_ $F) => `(<[ `([$F]) ]>)
  | _ => throw ()

@[app_unexpander wpgen.fail]
def unexpandWpgenFail : Lean.PrettyPrinter.Unexpander
  | `($_) => `(<[ Fail ]>)

@[app_unexpander wpgen.val]
def unexpandWpgenVal : Lean.PrettyPrinter.Unexpander
  | `($_ $v) => `(<[ Val $v ]>)
  | _ => throw ()

@[app_unexpander wpgen.let]
def unexpandWpgenLet : Lean.PrettyPrinter.Unexpander
  | `($_ $F1 $F2) => do
    let F1 ← parseToXwp F1
    match F2 with
    | `(fun $x:ident => $F2) =>
      let F2 ← parseToXwp F2
      `(<[ Let $x := $F1 in $F2 ]>)
    | _ => `(<[ Let x := $F1 in [$F2 x] ]>)
  | _ => throw ()

@[app_unexpander wpgen.seq]
def unexpandWpgenSeq : Lean.PrettyPrinter.Unexpander
  | `($_ $F1 $F2) => do
    let F1 ← parseToXwp F1
    let F2 ← parseToXwp F2
    `(<[ Seq $F1 ; $F2 ]>)
  | _ => throw ()

@[app_unexpander wpgen.app]
def unexpandWpgenApp : Lean.PrettyPrinter.Unexpander
  | `($_ $t) => do
    let t ← parseToSlf t
    `(<[ App $t ]>)
  | _ => throw ()

@[app_unexpander wpgen.if]
def unexpandWpgenIf : Lean.PrettyPrinter.Unexpander
  | `($_ $t $F1 $F2) => do
    let t ← parseToSlf t
    let F1 ← parseToXwp F1
    let F2 ← parseToXwp F2
    `(<[ If $t Then $F1 Else $F2 ]>)
  | _ => throw ()

@[app_unexpander wpgen.fun]
def unexpandWpgenFun : Lean.PrettyPrinter.Unexpander
  | `($_ $F) => do
    match F with
    | `(fun $x:ident => $F) =>
      let F ← parseToXwp F
      `(<[ Fun $x => $F ]>)
    | _ => `(<[ Fun x => [$F x] ]>)
  | _ => throw ()

@[app_unexpander wpgen.fix]
def unexpandWpgenFix : Lean.PrettyPrinter.Unexpander
  | `($_ $F) => do
    match F with
    | `(fun $f:ident $x:ident => $F) =>
      let F ← parseToXwp F
      `(<[ Fix $f $x => $F ]>)
    | _ => `(<[ Fix f x => [$F f x] ]>)
  | _ => throw ()

namespace WPGen.XWPNotationExamples
open XLemmas

def incr: Val := [slf|
    vfun p =>
      let n := !p in
      let m := n + 1 in
      p := m
  ]

theorem incr_spec (p: Loc) (n: Int):
  Triple (.app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n + 1: Int))
:= by
  apply xwp_fun rfl; simp [wpgen, Term.isubst]
  apply xstruct; apply xlet
  apply xstruct; apply xapp (Triple.get); xsimp
  apply xstruct; apply xlet
  apply xstruct; apply xapp (Triple.add); xsimp
  apply xstruct; apply xapp (Triple.set)
  xsimp

def succ_using_incr : Val := [slf|
  vfun n =>
    let r := ref n in
    [incr] r;
    let x := ! r in
    free r;
    x
]

example:
  forall n: Int, Triple (.app succ_using_incr n)
    \[]
    (fun r => \[r = (n + 1: Int)])
:= by
  intro n
  apply xwp_fun rfl; simp [wpgen, Term.isubst, wpgen.var]
  apply xstruct; apply xlet
  apply xstruct; apply xapp (Triple.ref); xsimp
  intro x p E; simp_all only []
  apply xstruct; apply xseq
  apply xstruct; apply xapp; (apply incr_spec _ _); (try any_goals xsimp)
  apply xstruct; apply xlet
  apply xstruct; apply xapp (Triple.get); xsimp
  apply xstruct; apply xseq
  apply xstruct; apply xapp (Triple.free); xsimp
  apply xstruct; apply xval
  xsimp

def factorial: Val := [slf|
  vfix f n =>
    let b := n > 0 in
    if b then
      let n' := n - 1 in
      let r := f n' in
      n * r
    else 1
]

-- Note this is not `_root_.Nat.factorial` but `Nat.factorial` in the current namespace
def Nat.factorial: Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * Nat.factorial n

example (n: Nat):
  Triple (.app factorial n)
    \[]
    (fun r => \[r = (Nat.factorial n)])
:= by
  induction n
  case zero =>
    simp [Nat.factorial]
    apply xwp_fix rfl (by simp); simp [wpgen, Term.isubst]
    apply xstruct; apply xlet
    apply xstruct; apply xapp (Triple.gt); xsimp
    apply xstruct; apply xif_false
    apply xstruct; apply xval; xsimp
  case succ n IH =>
    apply xwp_fix rfl (by simp); simp [wpgen, Term.isubst]
    apply xstruct; apply xlet
    apply xstruct; apply xapp (Triple.gt); xsimp
    apply xstruct; apply xif_true
    apply xstruct; apply xlet
    apply xstruct; apply xapp (Triple.sub); xsimp
    apply xstruct; apply xlet
    apply xstruct; apply xapp (IH); xsimp
    apply xstruct; apply xapp (Triple.mul); xsimp
    simp [Nat.factorial]

-- if
example {n: Int} {p: Loc}:
  let is3: Val := [slf|
    vfun x =>
      let v := !x in
      let t := v == 3 in
      if t then true else false
  ]
  Triple
    (.app is3 p)
    (p ~~> n)
    (fun r => p ~~> n ** \[r = (n == 3)])
:= by
  intro is3
  apply xwp_fun rfl;
  simp [wpgen, Term.isubst]
  apply xstruct; apply xlet
  apply xstruct; apply xapp (Triple.get); xsimp
  apply xstruct; apply xlet
  apply xstruct; apply xapp (Triple.eq); xsimp
  apply xstruct; apply xif
  . -- case true
    intro H
    simp_all
    apply xstruct; apply xval; xsimp
  . -- case false
    intro H
    simp_all
    apply xstruct; apply xval; xsimp
    exact H

-- fun
def createCounter: Val := [slf|
  vfun c =>
    let p := ref 0 in
    fun u =>
      [incr] p;
      !p
]

def CounterSpec (f: Val) (p: Loc) : Prop :=
  forall m: Int,
    Triple [slf| [f] unit ]
      (p ~~> m)
      (fun r => \[r = (m + 1: Int)] ** p ~~> (m+1: Int))

example:
  Triple [slf| [createCounter] unit ]
    \[]
    (fun f => \∃ p, (p ~~> 0) ** \[CounterSpec f p])
:= by
  apply xwp_fun (rfl); simp [wpgen, Term.isubst]
  apply xstruct; apply xlet
  apply xstruct; apply xapp (Triple.ref); xsimp
  intro x p E; cases E
  apply xstruct; apply xfun_nospec; any_goals xsimp
  intro vf H
  simp [CounterSpec]
  intro m
  apply H
  apply xstruct; apply xseq
  apply xstruct; apply xapp (incr_spec _ _); (try any_goals xsimp)
  apply xstruct; apply xapp (Triple.get); xsimp

-- fix
def createSlowAddTo: Val := [slf|
  vfun n =>
    fix f x =>
      let b := x > 0 in
      if b then
        let x' := x - 1 in
        let r := f x' in
        1 + r
      else n
]

def SlowAddToSpec (f: Val) (n: Int) : Prop :=
  forall x: Int,
    Triple [slf| [f] [x] ]
      \[x > 0]
      (fun r => \[r = x + n])

example (n: Int):
  Triple [slf| [createSlowAddTo] [n] ]
    \[]
    (fun f => \[SlowAddToSpec f n])
:= by
  apply xwp_fun (rfl); simp [wpgen, Term.isubst]
  apply xstruct; apply xfix_nospec
  simp [SlowAddToSpec]
  xsimp; simp [wpgen.var]
  intro vf Hf vx
  cases vx
  case negSucc =>
    grind
  case ofNat nx =>
    simp
    induction nx
    case zero =>
      apply Hf; xsimp
    case succ nx' IH =>
      apply Hf; xsimp
      apply xstruct; apply xlet
      apply xstruct; apply xapp (Triple.gt); xsimp
      apply xstruct; apply xif_true
      apply xstruct; apply xlet
      apply xstruct; apply xapp (Triple.sub); xsimp
      apply xstruct; apply xlet
      cases nx'
      case zero =>
        specialize Hf 0 \[];
        apply xstruct; apply xapp; apply Hf; any_goals xsimp
        apply xstruct; apply xlet
        apply xstruct; apply xapp (Triple.gt); xsimp
        apply xstruct; apply xif_false
        intro _
        apply xstruct; apply xval
        apply xstruct; apply xapp (Triple.add); xsimp
      case succ nx' =>
        apply xstruct; apply xapp (IH); xsimp
        apply xstruct; apply xapp (Triple.add); xsimp
        omega

end WPGen.XWPNotationExamples
end Notations
