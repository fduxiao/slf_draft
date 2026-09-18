import Lean
import SLF.Map


namespace SLF.Lang
open Map

/-!
## Definition of the language
-/
inductive Prim: Type where
  | ref : Prim
  | get : Prim
  | set : Prim
  | free : Prim
  | neg : Prim
  | opp : Prim
  | eq : Prim
  | add : Prim
  | neq : Prim
  | sub : Prim
  | mul : Prim
  | div : Prim
  | mod : Prim
  | rand : Prim
  | le : Prim
  | lt : Prim
  | ge : Prim
  | gt : Prim
  | ptr_add : Prim
  deriving Inhabited, Repr


def Loc: Type := Nat deriving OfNat, Inhabited, Repr
def null: Loc := 0
def Var: Type := String deriving Inhabited, Repr

mutual

inductive Val : Type where
  | unit : Val
  | bool : Bool → Val
  | int : Int → Val
  | loc : Loc → Val
  | prim : Prim → Val
  | fun : Var → Term → Val
  | fix : Var → Var → Term → Val
  | uninit : Val
  | error : Val
  deriving Inhabited, Repr


inductive Term : Type where
  | val : Val → Term
  | var : Var → Term
  | fun : Var → Term → Term
  | fix : Var → Var → Term → Term
  | app : Term → Term → Term
  | seq : Term → Term → Term
  | let : Var → Term → Term → Term
  | if : Term → Term → Term → Term
  deriving Inhabited, Repr

end


instance: Coe Prim Val where
  coe := Val.prim


instance: Coe Val Term where
  coe := Term.val


instance: Coe String Term where
  coe := Term.var


instance: Coe Int Val where
  coe := Val.int


instance: Coe Int Term where
  coe := Term.val ∘ Val.int


instance: Coe Nat Val where
  coe := Val.int ∘ Int.ofNat

instance {n}: OfNat Val n where
  ofNat := Val.int n


instance {n}: OfNat Term n where
  ofNat := Term.val (Val.int n)

/-!
## Custom syntax for the language
-/

declare_syntax_cat slf_term (behavior := symbol)
scoped syntax "[term| " slf_term " ]" : term
scoped syntax " [" term "] " : slf_term
scoped syntax " (" slf_term ") " : slf_term
-- variable
scoped syntax ident : slf_term
-- number
scoped syntax num : slf_term
-- application
scoped syntax:70 slf_term:70 slf_term:71 : slf_term
-- ite
scoped syntax:31 "if " slf_term:1 " then " slf_term:1 " else " slf_term:1 : slf_term
scoped syntax:31 "if " slf_term:1 " then " slf_term:1 " end" : slf_term
-- seq
scoped syntax:32 slf_term "; " slf_term:1 : slf_term
-- let
scoped syntax:32 "let " ident " := " slf_term:1 " in " slf_term:1 : slf_term
scoped syntax:32 "let " ident ident+ " := " slf_term:1 " in " slf_term:1 : slf_term
scoped syntax:32 "let " " rec " ident ident+ " := " slf_term:1 " in " slf_term:1 : slf_term
-- fun
scoped syntax:31 "fun " ident+ " => " slf_term:1 : slf_term
scoped syntax:31 "vfun " ident+ " => " slf_term:1 : slf_term
-- fix
scoped syntax:31 "fix " ident ident+ " => " slf_term:1 : slf_term
scoped syntax:31 "vfix " ident ident+ " => " slf_term:1 : slf_term
-- unit
scoped syntax "unit" : slf_term

-- primitives
scoped syntax "ref" : slf_term
scoped syntax "free": slf_term
scoped syntax "not": slf_term
scoped syntax "!" slf_term:33 : slf_term
scoped syntax ident " := " slf_term:33 : slf_term
scoped syntax "[" term "]" " := " slf_term:33 : slf_term
scoped syntax:42 slf_term:42 " + " slf_term:43 : slf_term
scoped syntax:43 "-" slf_term:99 : slf_term
scoped syntax:42 slf_term:42 " - " slf_term:43 : slf_term
scoped syntax:43 slf_term:43 " * " slf_term:44 : slf_term
scoped syntax:43 slf_term:43 " / " slf_term:44 : slf_term
scoped syntax:43 slf_term:43 " % " slf_term:44 : slf_term
scoped syntax:41 slf_term:41 " == " slf_term:42 : slf_term
scoped syntax:41 slf_term:41 " != " slf_term:42 : slf_term
scoped syntax:40 slf_term:40 " <= " slf_term:41 : slf_term
scoped syntax:40 slf_term:40 " < " slf_term:41 : slf_term
scoped syntax:40 slf_term:40 " >= " slf_term:41 : slf_term
scoped syntax:40 slf_term:40 " > " slf_term:41 : slf_term


scoped macro_rules
| `([term| [$t] ]) => `((($t): Term))
| `([term| ( $t ) ]) => `([term| $t ])
| `([term| $t:ident ]) => `(Term.var $(Lean.quote t.getId.toString))
| `([term| $t:num ]) => `(Val.int $(Lean.quote t.getNat))
| `([term| $t1 $t2 ]) => `(Term.app [term| $t1 ] [term| $t2 ])
| `([term| if $t1 then $t2 else $t3 ]) => `(Term.if [term| $t1 ] [term| $t2 ] [term| $t3 ])
| `([term| if $t1 then $t2 end ]) => `(Term.if [term| $t1 ] [term| $t2 ] (Term.val (Val.unit)))
| `([term| $t1 ; $t2 ]) => `(Term.seq [term| $t1 ] [term| $t2 ])
| `([term| let $x := $t1 in $t2 ]) => `(Term.let $(Lean.quote x.getId.toString) [term| $t1 ] [term| $t2 ])
| `([term| let $x $y* := $t1 in $t2 ]) => `(Term.let $(Lean.quote x.getId.toString) [term| fun $y* => $t1 ] [term| $t2 ])
| `([term| let rec $f $x* := $t1 in $t2 ]) => `(Term.let $(Lean.quote f.getId.toString) [term| fix $f $x* => $t1 ] [term| $t2 ])
| `([term| fun $x => $t ]) => `(Term.fun $(Lean.quote x.getId.toString) [term| $t ])
| `([term| fun $x1 $x2* => $t ]) => `(Term.fun $(Lean.quote x1.getId.toString) [term| fun $x2* => $t ])
| `([term| vfun $x => $t ]) => `(Val.fun $(Lean.quote x.getId.toString) [term| $t ])
| `([term| vfun $x1 $x2* => $t ]) => `(Val.fun $(Lean.quote x1.getId.toString) [term| fun $x2* => $t ])
| `([term| fix $f $x => $t ]) => `(Term.fix $(Lean.quote f.getId.toString) $(Lean.quote x.getId.toString) [term| $t ])
| `([term| fix $f $x1 $x2* => $t ]) => `(Term.fix $(Lean.quote f.getId.toString) $(Lean.quote x1.getId.toString) [term| fun $x2* => $t ])
| `([term| vfix $f $x => $t ]) => `(Val.fix $(Lean.quote f.getId.toString) $(Lean.quote x.getId.toString) [term| $t ])
| `([term| vfix $f $x1 $x2* => $t ]) => `(Val.fix $(Lean.quote f.getId.toString) $(Lean.quote x1.getId.toString) [term| fun $x2* => $t ])
| `([term| unit ]) => `(Val.unit)
-- primitives
| `([term| ref ]) => `(Val.prim Prim.ref)
| `([term| free ]) => `(Val.prim Prim.free)
| `([term| not ]) => `(Val.prim Prim.neg)
| `([term| ! $t ]) => `(Term.app (Prim.get) [term| $t ])
| `([term| $t1:ident := $t2 ]) => `(Term.app (Term.app Prim.set [term| $t1:ident ]) [term| $t2 ])
| `([term| [$t1] := $t2 ]) => `(Term.app (Term.app Prim.set [term| [$t1] ]) [term| $t2 ])
| `([term| $t1 + $t2 ]) => `(Term.app (Term.app Prim.add [term| $t1 ]) [term| $t2 ])
| `([term| - $t ]) => `(Term.app Prim.opp [term| $t ])
| `([term| $t1 - $t2 ]) => `(Term.app (Term.app Prim.sub [term| $t1 ]) [term| $t2 ])
| `([term| $t1 * $t2 ]) => `(Term.app (Term.app Prim.mul [term| $t1 ]) [term| $t2 ])
| `([term| $t1 / $t2 ]) => `(Term.app (Term.app Prim.div [term| $t1 ]) [term| $t2 ])
| `([term| $t1 % $t2 ]) => `(Term.app (Term.app Prim.mod [term| $t1 ]) [term| $t2 ])
| `([term| $t1 == $t2 ]) => `(Term.app (Term.app Prim.eq [term| $t1 ]) [term| $t2 ])
| `([term| $t1 != $t2 ]) => `(Term.app (Term.app Prim.neq [term| $t1 ]) [term| $t2 ])
| `([term| $t1 <= $t2 ]) => `(Term.app (Term.app Prim.le [term| $t1 ]) [term| $t2 ])
| `([term| $t1 < $t2 ]) => `(Term.app (Term.app Prim.lt [term| $t1 ]) [term| $t2 ])
| `([term| $t1 >= $t2 ]) => `(Term.app (Term.app Prim.ge [term| $t1 ]) [term| $t2 ])
| `([term| $t1 > $t2 ]) => `(Term.app (Term.app Prim.gt [term| $t1 ]) [term| $t2 ])

example: [term| p.a] = Term.var "p.a" := rfl
example: [term| !p] = Term.app Prim.get (Term.var "p") := rfl
example: [term| !["x"]] = Term.app Prim.get (Term.var "x") := rfl
example: [term| (!["x"]) ; (!["y"])] =
  Term.seq
  (Term.app Prim.get "x")
  (Term.app Prim.get "y")
:= rfl
example: [term| !(["x"] ; !["y"])] =
  Term.app
  Prim.get
  (.seq "x" $ Term.app Prim.get "y")
:= rfl
example: [term| !x ; !y] =
  Term.seq
  (.app Prim.get "x")
  (.app Prim.get "y")
:= rfl
example: [term| !["x"] ; !y] =
  Term.seq
  (.app Prim.get "x")
  (.app Prim.get "y")
:= rfl
example: [term| if !x then y else !z] =
  Term.if
  (.app Prim.get "x")
  "y"
  (.app Prim.get "z")
:= rfl
example: [term| if !x then y; z else !z] =
  Term.if
  (.app Prim.get "x")
  (.seq "y" "z")
  (.app Prim.get "z")
:= rfl
example: [term| let x := !y in z] =
  Term.let "x" (.app Prim.get "y") "z"
:= rfl
example: [term| fun x => y z] =
  Term.fun "x" (.app "y" "z")
:= rfl
example: [term| (fun x => y) z] =
  Term.app (Term.fun "x" "y") "z"
:= rfl
example: [term| fun x => y] =
  Term.fun "x" "y"
:= rfl
example: [term| fun x y => z] =
  Term.fun "x" (Term.fun "y" "z")
:= rfl
example: [term| fun x y z => w] =
  Term.fun "x" (Term.fun "y" (Term.fun "z" "w"))
:= rfl
example: [term| let f x := z in f w] =
  Term.let "f" (Term.fun "x" "z") (.app "f" "w")
:= rfl
example: [term| fix f x => y] =
  Term.fix "f" "x" "y"
:= rfl
example: [term| fix f x z w => y] =
  Term.fix "f" "x" (Term.fun "z" (Term.fun "w" "y"))
:= rfl
example: [term| vfix f x => y] =
  Val.fix "f" "x" "y"
:= rfl
example: [term| let rec f x := y in z] =
  Term.let "f" (.fix "f" "x" "y") "z"
:= rfl
example: [term| let rec f x y := y in z] =
  Term.let "f" (.fix "f" "x" (.fun "y" "y")) "z"
:= rfl
example: [term| let rec f x y := y in [let x := "x"; x ++ "y"] := z] =
  Term.let "f" (.fix "f" "x" (.fun "y" "y")) (.app (.app Prim.set "xy") "z")
:= rfl
example: [term| x + y + z] =
  Term.app (.app Prim.add (.app (.app Prim.add "x") "y")) "z"
:= rfl
example: [term| x + t * z] =
  Term.app (.app Prim.add "x") (.app (.app Prim.mul "t") "z")
:= rfl

example: [term| (x + t) * z] =
  Term.app (.app Prim.mul (.app (.app Prim.add "x") "t")) "z"
:= rfl
example: [term| x + t * z - y] =
  Term.app (.app Prim.sub (.app (.app Prim.add "x") (.app (.app Prim.mul "t") "z"))) "y"
:= rfl
example: [term| x + - t * z - y % z] =
  Term.app
    (.app Prim.sub
      (.app (.app Prim.add "x")
      (.app (.app Prim.mul (.app Prim.opp "t")) "z"))
    )
    (.app (.app Prim.mod "y") "z")
:= rfl
-- test comparison operators
example: [term| x == y == z] =
  Term.app (.app Prim.eq (.app (.app Prim.eq "x") "y")) "z"
:= rfl
example: [term| x != y] =
  Term.app (.app Prim.neq "x") "y"
:= rfl
example: [term| x * w <= y + z] =
  Term.app (.app Prim.le (.app (.app Prim.mul "x") "w")) (.app (.app Prim.add "y") "z")
:= rfl
example {f}: [term| let f x := x in [f] < y < z] =
  Term.let "f" (.fun "x" "x") (.app (.app Prim.lt (.app (.app Prim.lt f) "y")) "z")
:= rfl

example: [term| let f x := x + 3 in f < y < z] =
  Term.let "f" (.fun "x" (.app (.app Prim.add "x") 3)) (.app (.app Prim.lt (.app (.app Prim.lt "f") "y")) "z")
:= rfl


/-!
## Pretty printing of the language
-/

section
open Lean Elab Command Term PrettyPrinter Delaborator

@[app_unexpander Val.int]
def unexpandValInt: Unexpander
  | `($_ $x:num ) => `([term| $x:num])
  | _ => throw ()


@[app_unexpander Val.unit]
def unexpandValUnit: Unexpander
  | `($_) => `([term| unit ])


@[app_unexpander Val.fun]
def unexpandValFun: Unexpander
  | `($_ $x:str [term| $b]) =>
    let name := mkIdent (Lean.Name.mkStr1 x.getString)
    match b with
    | `(slf_term| fun $x* => $b) => `([term| vfun $name $x* => $b ])
    | `(slf_term| $t ) => `([term| vfun $name => $t ])
  | _ => throw ()


@[app_unexpander Val.fix]
def unexpandValFix: Unexpander
  | `($_ $f:str $x:str [term| $b]) =>
    let name_f := mkIdent (Lean.Name.mkStr1 f.getString)
    let name_x := mkIdent (Lean.Name.mkStr1 x.getString)
    match b with
    | `(slf_term| fun $x* => $b) => `([term| vfix $name_f $name_x $x* => $b ])
    | `(slf_term| $t ) => `([term| vfix $name_f $name_x => $t ])
  | _ => throw ()


@[app_unexpander Val.prim]
def unexpandValPrim: Unexpander
  | `($_ $p) =>
    match p with
    | `(Prim.ref) => `([term| ref ])
    | `(Prim.free) => `([term| free ])
    | `(Prim.neg) => `([term| not ])
    | _ => throw ()
  | _ => throw ()


@[app_unexpander Term.var]
def unexpandVar: Unexpander
  | `($_ $x:str) =>
    let name := mkIdent (Lean.Name.mkStr1 x.getString)
    `([term| $name:ident ])
  | `($_ $x:term) => `([term| [$x] ])
  | _ => throw ()


@[app_unexpander Term.val]
def unexpandVal: Unexpander
  | `($_ [term| $n:num ]) => `([term| $n:num])
  | `($_ $x:num) => `([term| $x:num])
  | `($_ [term| unit ]) => `([term| unit ])
  | `($_ [term| vfun $x* => $t ]) => `([term| vfun $x* => $t ])
  | `($_ [term| vfix $f $x* => $t ]) => `([term| vfix $f $x* => $t ])
  | `($_ $x:term) => `([term| [$x] ])
  | _ => throw ()


def unexpandAppArg: TSyntax `slf_term → UnexpandM (TSyntax `slf_term)
  | `(slf_term| $f $x ) => `(slf_term| ($f $x))
  | t => `(slf_term| $t)


def unexpandAppFun: TSyntax `slf_term → UnexpandM (TSyntax `slf_term)
  | `(slf_term| $f $x ) => `(slf_term| $f $x)
  | `(slf_term| [$t] ) => `(slf_term| [$t])
  | `(slf_term| $i:ident ) => `(slf_term| $i:ident)
  | f => `(slf_term| ($f))


@[app_unexpander Term.app]
def unexpandApp: Unexpander
  | `($_ [term| $f] [term| $a ]) => do
    let a' ← unexpandAppArg a
    let f' ← unexpandAppFun f
    let t ← `(slf_term|$f' $a')
    match t with
    | `(slf_term| [Val.prim Prim.get] $a) => `([term| ! $a ])
    | `(slf_term| [Val.prim Prim.set] $a:ident $b) => `([term| $a:ident := $b ])
    | `(slf_term| [Val.prim Prim.set] [$t] $b) => `([term| [$t] := $b ])
    | `(slf_term| [Val.prim Prim.add] $a $b) => `([term| $a + $b ])
    | t => `([term| $t ])
  | _ => throw ()


@[app_unexpander Term.if]
def unexpandIf: Unexpander
  | `($_ [term| $cond] [term| $t] [term| $f]) =>
    match f with
    | `(slf_term| unit ) => `([term| if $cond then $t end ])
    | `(slf_term| $f) => `([term| if $cond then $t else $f ])
  | _ => throw ()


@[app_unexpander Term.seq]
def unexpandSeq: Unexpander
  | `($_ [term| $a] [term| $b ]) => `([term| $a; $b ])
  | _ => throw ()


@[app_unexpander Term.fun]
def unexpandFun: Unexpander
  | `($_ $x:str $a) =>
    let name := mkIdent (Lean.Name.mkStr1 x.getString)
    match a with
    | `([term| fun $x* => $a ]) => `([term| fun $name $x* => $a ])
    | `([term| $t ]) => `([term| fun $name => $t ])
    | _ => throw ()
  | _ => throw ()


@[app_unexpander Term.fix]
def unexpandFix: Unexpander
  | `($_ $f:str $x:str $a) =>
    let name_f := mkIdent (Lean.Name.mkStr1 f.getString)
    let name_x := mkIdent (Lean.Name.mkStr1 x.getString)
    match a with
    | `([term| fun $x* => $a ]) => `([term| fix $name_f $name_x $x* => $a ])
    | `([term| $t ]) => `([term| fix $name_f $name_x => $t ])
    | _ => throw ()
  | _ => throw ()


@[app_unexpander Term.let]
def unexpandLet: Unexpander
  | `($_ $x:str [term| $v ] [term| $b ]) =>
    let name := mkIdent (Lean.Name.mkStr1 x.getString)
    match v with
    | `(slf_term| fun $x* => $v ) => `([term| let $name $x* := $v in $b ])
    | `(slf_term| fix $_ $x* => $v ) => `([term| let rec $name $x* := $v in $b ])
    | `(slf_term| $v ) => `([term| let $name := $v in $b ])
  | _ => throw ()

scoped elab "slf_pp" stx:term:51: term => do
  let expr ← elabTerm stx none
  let pretty ← ppExpr expr
  let str := toString pretty
  pure <| toExpr str

end

namespace TestPrettyPrinter

/--
Evaluate the pretty printer on a term. Since I am going to compare the result using `=`,
the precedence of `pp` should be higher than that of `=`.
-/

def num: Val := 3
def x: String := "x"

-- values
#guard slf_pp Val.int 3 = "[term| 3 ]"
#guard slf_pp [term| 3] = "[term| 3 ]"
#guard slf_pp [term| [3]] = "3"  -- ofNat is just a `3`
#guard slf_pp ([term| 3] : Term) = "[term| 3 ]"
#guard slf_pp Term.val num = "[term| [num] ]"
#guard slf_pp Val.unit = "[term| unit ]"
#guard slf_pp Term.val Val.unit = "[term| unit ]"
#guard slf_pp [term| unit] = "[term| unit ]"
#guard slf_pp ([term| unit]: Term) = "[term| unit ]"
#guard slf_pp Val.fun "x" [term| x] = "[term| vfun x => x ]"
#guard slf_pp [term| vfun a => b] = "[term| vfun a => b ]"
#guard slf_pp ([term| vfun a => b]: Term) = "[term| vfun a => b ]"
#guard slf_pp [term| vfun x => fun y => fun z => z] = "[term| vfun x y z => z ]"
#guard slf_pp Val.fix "f" "x" [term| x] = "[term| vfix f x => x ]"
#guard slf_pp [term| vfix f a => b] = "[term| vfix f a => b ]"
#guard slf_pp ([term| vfix f a => b]: Term) = "[term| vfix f a => b ]"
#guard slf_pp [term| vfix f a => fun b => c] = "[term| vfix f a b => c ]"

-- terms
#guard slf_pp Term.var x = "[term| [x] ]"
#guard slf_pp [term| x] = "[term| x ]"
#guard slf_pp [term| ["x"]] = "[term| x ]"
#guard slf_pp [term| [x ++ "y"] y z] = "[term| [x ++ \"y\"] y z ]"
#guard slf_pp [term| (x y) z] = "[term| x y z ]"
#guard slf_pp [term| x (y z)] = "[term| x (y z) ]"
#guard slf_pp [term| x (y (z w))] = "[term| x (y (z w) ) ]"
#guard slf_pp [term| x (y z) w] = "[term| x (y z) w ]"
#guard slf_pp [term| x y z w] = "[term| x y z w ]"
#guard slf_pp [term| [x] y z w] = "[term| [x] y z w ]"
#guard slf_pp [term| [x] y [x] w] = "[term| [x] y [x] w ]"
#guard slf_pp [term| [x] (y [x]) w] = "[term| [x] (y [x] ) w ]"
#guard slf_pp [term| if x then y else z] = "[term| if x then y else z ]"
#guard slf_pp [term| if x then y end] = "[term| if x then y end ]"
#guard slf_pp [term| if [x] then y; z else w] = "[term| if [x] then y; z else w ]"
#guard slf_pp [term| (fun x => x y) z] = "[term| (fun x => x y) z ]"
#guard slf_pp [term| fun x => (x y z)] = "[term| fun x => x y z ]"
#guard slf_pp [term| fun x => fun y => fun z => z] = "[term| fun x y z => z ]"
#guard slf_pp [term| (fun x y => fun z => z) w] = "[term| (fun x y z => z) w ]"
#guard slf_pp [term| if [x] then y; z else w] = "[term| if [x] then y; z else w ]"
#guard slf_pp [term| (if [x] then y; z else w) c] = "[term| (if [x] then y; z else w) c ]"
#guard slf_pp [term| (fix f x => x y) z] = "[term| (fix f x => x y) z ]"
#guard slf_pp [term| (fix f x y => x y) z] = "[term| (fix f x y => x y) z ]"
#guard slf_pp [term| (fix f x y z => x y) z] = "[term| (fix f x y z => x y) z ]"
#guard slf_pp [term| (fix f x => fun y => fun z => x y) z] = "[term| (fix f x y z => x y) z ]"
#guard slf_pp [term| (fix f x => fun y => fun z => x y) z] = "[term| (fix f x y z => x y) z ]"
#guard slf_pp [term| (fix f x => fun y => if x then y; fun z => x y else z) z] = "[term| (fix f x y => if x then y; fun z => x y else z) z ]"
-- let rules
#guard slf_pp [term| let x := y in z] = "[term| let x := y in z ]"
#guard slf_pp [term| let x y := z in w] = "[term| let x y := z in w ]"
#guard slf_pp [term| let rec f x := y in z] = "[term| let rec f x := y in z ]"
#guard slf_pp [term| let rec f x y := z in w] = "[term| let rec f x y := z in w ]"
#guard slf_pp [term| let rec f x y := z in [x] w] = "[term| let rec f x y := z in [x] w ]"
-- primitives
-- `ref`, `free`, `not` are printed as is
def prim := Val.prim Prim.get
#guard slf_pp prim = "prim"
#guard slf_pp [term| [prim]] = "[term| [prim] ]"
#guard slf_pp [term| ref] = "[term| ref ]"
#guard slf_pp [term| free] = "[term| free ]"
#guard slf_pp [term| not] = "[term| not ]"
-- the rest must be application of the primitive to its arguments
-- get
#guard slf_pp (Term.app (Val.prim Prim.get) x) = "[term| ! [x] ]"
#guard slf_pp [term| !x] = "[term| !x ]"
#guard slf_pp [term| !!x] = "[term| !!x ]"
#guard slf_pp [term| ! x (x y)] = "[term| ! (x (x y) ) ]"
#guard slf_pp [term| ! x x y] = "[term| ! (x x y) ]"
-- assign
#guard slf_pp (Term.app (Term.app (Val.prim Prim.set) x) "y") = "[term| [x] := y ]"
-- arithmetic
#guard slf_pp (Term.app (Term.app (Val.prim Prim.add) x) "y") = "[term| [x] + y ]"
