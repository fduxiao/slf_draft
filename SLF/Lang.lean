import SLF.Map


namespace SLF.Lang
open Map

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


inductive Term : Type where
  | val : Val → Term
  | var : Var → Term
  | fun : Var → Term → Term
  | fix : Var → Var → Term → Term
  | app : Term → Term → Term
  | seq : Term → Term → Term
  | let : Var → Term → Term → Term
  | if : Term → Term → Term → Term
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


instance: OfNat Val n where
  ofNat := Val.int n


instance: OfNat Term n where
  ofNat := Term.val (Val.int n)


declare_syntax_cat slf_term (behavior := symbol)
scoped syntax "[term| " slf_term " ]" : term
scoped syntax " [" term "] " : slf_term
scoped syntax " (" slf_term ") " : slf_term
-- variable
scoped syntax ident : slf_term
-- number
scoped syntax num : slf_term
-- application
scoped syntax:70 slf_term:71 slf_term:70 : slf_term
-- ite
scoped syntax:31 " if " slf_term:1 " then " slf_term:1 " else " slf_term:1 : slf_term
scoped syntax:31 " if " slf_term:1 " then " slf_term:1 " end " : slf_term
-- seq
scoped syntax:32 slf_term " ; " slf_term:1 : slf_term
-- let
scoped syntax:32 " let " ident " := " slf_term:1 " in " slf_term:1 : slf_term
scoped syntax:32 " let " ident ident+ " := " slf_term:1 " in " slf_term:1 : slf_term
scoped syntax:32 " let " " rec " ident ident+ " := " slf_term:1 " in " slf_term:1 : slf_term
-- fun
scoped syntax:31 " fun " ident+ "=>" slf_term:1 : slf_term
scoped syntax:31 " vfun " ident+ "=>" slf_term:1 : slf_term
-- fix
scoped syntax:31 " fix " ident ident+ "=>" slf_term:1 : slf_term
scoped syntax:31 " vfix " ident ident+ "=>" slf_term:1 : slf_term
-- unit
scoped syntax "unit" : slf_term

-- primitives
scoped syntax "ref" : slf_term
scoped syntax "free": slf_term
scoped syntax "not": slf_term
scoped syntax " ! " slf_term:33 : slf_term
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
| `([term| $t:num ]) => `(Term.val (Val.int $(Lean.quote t.getNat)))
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
