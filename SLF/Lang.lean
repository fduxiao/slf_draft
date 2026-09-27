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
  deriving Inhabited, Repr, BEq, DecidableEq


def Loc: Type := Nat deriving OfNat, Inhabited, Repr, BEq, DecidableEq, HAdd

@[simp]
def Loc.toNat (l: Loc): Nat := l
@[simp]
def Loc.toInt (l: Loc): Int := Int.ofNat l


instance: Coe Nat Loc where
  coe x := x

instance {n}: OfNat Loc n where
  ofNat := n

instance: HAdd Loc Int Loc where
  hAdd x y := (x.toInt + y).toNat

def null: Loc := 0
abbrev Var: Type := String

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
  deriving Inhabited, Repr, BEq, DecidableEq


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

instance: Coe Loc Val where
  coe := Val.loc

instance: Coe Int Val where
  coe := Val.int

instance: Coe Nat Val where
  coe i := Val.int (Int.ofNat i)

instance: Coe Bool Val where
  coe := Val.bool

instance {n}: OfNat Val n where
  ofNat := Val.int n

instance: Coe Val Term where
  coe := Term.val

instance: Coe String Term where
  coe := Term.var


instance {n}: OfNat Term n where
  ofNat := Term.val (Val.int n)


def Term.loc (l: Loc): Term := Term.val (Val.loc l)

/-!
## Custom syntax for the language
-/

declare_syntax_cat slf_term (behavior := symbol)
scoped syntax "[slf| " slf_term " ]" : term
scoped syntax " [" term "] " : slf_term
scoped syntax " (" slf_term ") " : slf_term
-- variable
scoped syntax ident : slf_term
-- number
scoped syntax num : slf_term
-- boolean
scoped syntax "true" : slf_term
scoped syntax "false" : slf_term
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
scoped syntax "rand": slf_term
scoped syntax "!" slf_term:33 : slf_term
scoped syntax ident " := " slf_term:33 : slf_term
scoped syntax "[" term "]" " := " slf_term:33 : slf_term
-- ptr_add
-- ptr +> a + b +> c * d will be parsed as ptr +> (a + b) +> (c * d)
scoped syntax:42 slf_term:42 " +> " slf_term:43 : slf_term
-- arithmetic
scoped syntax:43 slf_term:43 " + " slf_term:44 : slf_term
scoped syntax:44 "-" slf_term:44 : slf_term
scoped syntax:43 slf_term:43 " - " slf_term:44 : slf_term
scoped syntax:44 slf_term:44 " * " slf_term:45 : slf_term
scoped syntax:44 slf_term:44 " / " slf_term:45 : slf_term
scoped syntax:44 slf_term:44 " % " slf_term:45 : slf_term
scoped syntax:41 slf_term:41 " == " slf_term:42 : slf_term
scoped syntax:41 slf_term:41 " != " slf_term:42 : slf_term
scoped syntax:40 slf_term:40 " <= " slf_term:41 : slf_term
scoped syntax:40 slf_term:40 " < " slf_term:41 : slf_term
scoped syntax:40 slf_term:40 " >= " slf_term:41 : slf_term
scoped syntax:40 slf_term:40 " > " slf_term:41 : slf_term


scoped macro_rules
| `([slf| [$t] ]) => `((($t): Term))
| `([slf| ( $t ) ]) => `([slf| $t ])
| `([slf| $t:ident ]) => `(Term.var $(Lean.quote t.getId.toString))
| `([slf| $t:num ]) => `(Val.int $(Lean.quote t.getNat))
| `([slf| $t1 $t2 ]) => `(Term.app [slf| $t1 ] [slf| $t2 ])
| `([slf| if $t1 then $t2 else $t3 ]) => `(Term.if [slf| $t1 ] [slf| $t2 ] [slf| $t3 ])
| `([slf| if $t1 then $t2 end ]) => `(Term.if [slf| $t1 ] [slf| $t2 ] (Term.val (Val.unit)))
| `([slf| $t1 ; $t2 ]) => `(Term.seq [slf| $t1 ] [slf| $t2 ])
| `([slf| let $x := $t1 in $t2 ]) => `(Term.let $(Lean.quote x.getId.toString) [slf| $t1 ] [slf| $t2 ])
| `([slf| let $x $y* := $t1 in $t2 ]) => `(Term.let $(Lean.quote x.getId.toString) [slf| fun $y* => $t1 ] [slf| $t2 ])
| `([slf| let rec $f $x* := $t1 in $t2 ]) => `(Term.let $(Lean.quote f.getId.toString) [slf| fix $f $x* => $t1 ] [slf| $t2 ])
| `([slf| fun $x => $t ]) => `(Term.fun $(Lean.quote x.getId.toString) [slf| $t ])
| `([slf| fun $x1 $x2* => $t ]) => `(Term.fun $(Lean.quote x1.getId.toString) [slf| fun $x2* => $t ])
| `([slf| vfun $x => $t ]) => `(Val.fun $(Lean.quote x.getId.toString) [slf| $t ])
| `([slf| vfun $x1 $x2* => $t ]) => `(Val.fun $(Lean.quote x1.getId.toString) [slf| fun $x2* => $t ])
| `([slf| fix $f $x => $t ]) => `(Term.fix $(Lean.quote f.getId.toString) $(Lean.quote x.getId.toString) [slf| $t ])
| `([slf| fix $f $x1 $x2* => $t ]) => `(Term.fix $(Lean.quote f.getId.toString) $(Lean.quote x1.getId.toString) [slf| fun $x2* => $t ])
| `([slf| vfix $f $x => $t ]) => `(Val.fix $(Lean.quote f.getId.toString) $(Lean.quote x.getId.toString) [slf| $t ])
| `([slf| vfix $f $x1 $x2* => $t ]) => `(Val.fix $(Lean.quote f.getId.toString) $(Lean.quote x1.getId.toString) [slf| fun $x2* => $t ])
| `([slf| unit ]) => `(Val.unit)
| `([slf| true ]) => `(Val.bool true)
| `([slf| false ]) => `(Val.bool false)
-- primitives
| `([slf| ref ]) => `(Val.prim Prim.ref)
| `([slf| free ]) => `(Val.prim Prim.free)
| `([slf| not ]) => `(Val.prim Prim.neg)
| `([slf| rand ]) => `(Val.prim Prim.rand)
| `([slf| ! $t ]) => `(Term.app (Prim.get) [slf| $t ])
| `([slf| $t1:ident := $t2 ]) => `(Term.app (Term.app Prim.set [slf| $t1:ident ]) [slf| $t2 ])
| `([slf| [$t1] := $t2 ]) => `(Term.app (Term.app Prim.set [slf| [$t1] ]) [slf| $t2 ])
| `([slf| $t1 +> $t2 ]) => `(Term.app (Term.app Prim.ptr_add [slf| $t1 ]) [slf| $t2 ])
| `([slf| $t1 + $t2 ]) => `(Term.app (Term.app Prim.add [slf| $t1 ]) [slf| $t2 ])
| `([slf| - $t ]) => `(Term.app Prim.opp [slf| $t ])
| `([slf| $t1 - $t2 ]) => `(Term.app (Term.app Prim.sub [slf| $t1 ]) [slf| $t2 ])
| `([slf| $t1 * $t2 ]) => `(Term.app (Term.app Prim.mul [slf| $t1 ]) [slf| $t2 ])
| `([slf| $t1 / $t2 ]) => `(Term.app (Term.app Prim.div [slf| $t1 ]) [slf| $t2 ])
| `([slf| $t1 % $t2 ]) => `(Term.app (Term.app Prim.mod [slf| $t1 ]) [slf| $t2 ])
| `([slf| $t1 == $t2 ]) => `(Term.app (Term.app Prim.eq [slf| $t1 ]) [slf| $t2 ])
| `([slf| $t1 != $t2 ]) => `(Term.app (Term.app Prim.neq [slf| $t1 ]) [slf| $t2 ])
| `([slf| $t1 <= $t2 ]) => `(Term.app (Term.app Prim.le [slf| $t1 ]) [slf| $t2 ])
| `([slf| $t1 < $t2 ]) => `(Term.app (Term.app Prim.lt [slf| $t1 ]) [slf| $t2 ])
| `([slf| $t1 >= $t2 ]) => `(Term.app (Term.app Prim.ge [slf| $t1 ]) [slf| $t2 ])
| `([slf| $t1 > $t2 ]) => `(Term.app (Term.app Prim.gt [slf| $t1 ]) [slf| $t2 ])

example: [slf| p.a] = Term.var "p.a" := rfl
example: [slf| !p] = Term.app Prim.get (Term.var "p") := rfl
example: [slf| !["x"]] = Term.app Prim.get (Term.var "x") := rfl
example: [slf| (!["x"]) ; (!["y"])] =
  Term.seq
  (Term.app Prim.get "x")
  (Term.app Prim.get "y")
:= rfl
example: [slf| !(["x"] ; !["y"])] =
  Term.app
  Prim.get
  (.seq "x" $ Term.app Prim.get "y")
:= rfl
example: [slf| !x ; !y] =
  Term.seq
  (.app Prim.get "x")
  (.app Prim.get "y")
:= rfl
example: [slf| !["x"] ; !y] =
  Term.seq
  (.app Prim.get "x")
  (.app Prim.get "y")
:= rfl
example: [slf| if !x then y else !z] =
  Term.if
  (.app Prim.get "x")
  "y"
  (.app Prim.get "z")
:= rfl
example: [slf| if !x then y; z else !z] =
  Term.if
  (.app Prim.get "x")
  (.seq "y" "z")
  (.app Prim.get "z")
:= rfl
example: [slf| let x := !y in z] =
  Term.let "x" (.app Prim.get "y") "z"
:= rfl
example: [slf| fun x => y z] =
  Term.fun "x" (.app "y" "z")
:= rfl
example: [slf| (fun x => y) z] =
  Term.app (Term.fun "x" "y") "z"
:= rfl
example: [slf| fun x => y] =
  Term.fun "x" "y"
:= rfl
example: [slf| fun x y => z] =
  Term.fun "x" (Term.fun "y" "z")
:= rfl
example: [slf| fun x y z => w] =
  Term.fun "x" (Term.fun "y" (Term.fun "z" "w"))
:= rfl
example: [slf| let f x := z in f w] =
  Term.let "f" (Term.fun "x" "z") (.app "f" "w")
:= rfl
example: [slf| fix f x => y] =
  Term.fix "f" "x" "y"
:= rfl
example: [slf| fix f x z w => y] =
  Term.fix "f" "x" (Term.fun "z" (Term.fun "w" "y"))
:= rfl
example: [slf| vfix f x => y] =
  Val.fix "f" "x" "y"
:= rfl
example: [slf| let rec f x := y in z] =
  Term.let "f" (.fix "f" "x" "y") "z"
:= rfl
example: [slf| let rec f x y := y in z] =
  Term.let "f" (.fix "f" "x" (.fun "y" "y")) "z"
:= rfl
example: [slf| let rec f x y := y in [let x := "x"; x ++ "y"] := z] =
  Term.let "f" (.fix "f" "x" (.fun "y" "y")) (.app (.app Prim.set "xy") "z")
:= rfl
example: [slf| rand ] = Term.val (Val.prim Prim.rand) := rfl
example: [slf| rand (3 + x)] =
  Term.app Prim.rand (.app (.app Prim.add 3) "x")
:= rfl
example: [slf| (rand 3) + x] =
  Term.app (.app Prim.add (.app Prim.rand 3)) "x"
:= rfl
example: [slf| rand x + 3] =
  Term.app (.app Prim.add (.app Prim.rand "x")) 3
:= rfl
example: [slf| x + y + z] =
  Term.app (.app Prim.add (.app (.app Prim.add "x") "y")) "z"
:= rfl
example: [slf| x + t * z] =
  Term.app (.app Prim.add "x") (.app (.app Prim.mul "t") "z")
:= rfl
example: [slf| -(x + y)] = Term.app Prim.opp
  (.app (.app Prim.add "x") "y")
:= rfl
example: [slf| -x + y] =
  Term.app (.app Prim.add (Term.app Prim.opp "x")) "y"
:= rfl
example: [slf| -x * y] = Term.app Prim.opp
  (.app (.app Prim.mul "x") "y")
:= rfl
example: [slf| (-x) * y] =
  Term.app (.app Prim.mul (.app Prim.opp "x")) "y"
:= rfl
example: [slf| (x + t) * z] =
  Term.app (.app Prim.mul (.app (.app Prim.add "x") "t")) "z"
:= rfl
example: [slf| x + t * z - y] =
  Term.app (.app Prim.sub (.app (.app Prim.add "x") (.app (.app Prim.mul "t") "z"))) "y"
:= rfl
example: [slf| x + - t * z - y % z] =
  Term.app
    (.app Prim.sub
      (.app (.app Prim.add "x")
      (.app Prim.opp (.app (.app Prim.mul "t") "z")))
    )
    (.app (.app Prim.mod "y") "z")
:= rfl
-- ptr_add
example (ptr: Loc): (ptr: Term) = Term.val (Val.loc ptr) := rfl
example (ptr: Loc): [slf| [ptr] +> 3] =
  Term.app (.app Prim.ptr_add (Term.val (Val.loc ptr))) 3
:= rfl
example: [slf| x +> y +> z] =
  Term.app (.app Prim.ptr_add (.app (.app Prim.ptr_add "x") "y")) "z"
:= rfl
example: [slf| x +> y * z] =
  Term.app (.app Prim.ptr_add "x") (.app (.app Prim.mul "y") "z")
:= rfl
example: [slf| x +> y + z] =
  Term.app (.app Prim.ptr_add "x") (.app (.app Prim.add "y") "z")
:= rfl
example: [slf| x +> y + z +> 5 * w % 3] =
  Term.app
    (.app Prim.ptr_add
      (.app (.app Prim.ptr_add "x")
      (.app (.app Prim.add "y") "z")))
    (.app
      (.app Prim.mod (.app (.app Prim.mul 5) "w"))
      3)
:= rfl
-- test comparison operators
example: [slf| x == y == z] =
  Term.app (.app Prim.eq (.app (.app Prim.eq "x") "y")) "z"
:= rfl
example: [slf| x != y] =
  Term.app (.app Prim.neq "x") "y"
:= rfl
example: [slf| x * w <= y + z] =
  Term.app (.app Prim.le (.app (.app Prim.mul "x") "w")) (.app (.app Prim.add "y") "z")
:= rfl
example {f}: [slf| let f x := x in [f] < y < z] =
  Term.let "f" (.fun "x" "x") (.app (.app Prim.lt (.app (.app Prim.lt f) "y")) "z")
:= rfl
example: [slf| let f x := x + 3 in f < y < z] =
  Term.let "f" (.fun "x" (.app (.app Prim.add "x") 3)) (.app (.app Prim.lt (.app (.app Prim.lt "f") "y")) "z")
:= rfl
example: [slf| x +> 3 == y] =
  Term.app (.app Prim.eq (.app (.app Prim.ptr_add "x") 3)) "y"
:= rfl


/-!
## Pretty printing of the language
-/

section
open Lean Elab Command Term PrettyPrinter Delaborator

@[app_unexpander Val.int]
def unexpandValInt: Unexpander
  | `($_ $x:num) => `([slf| $x:num])
  | `($_ $x:ident) => `([slf| [$x:ident]])
  | `($_ $x:term) => `([slf| [$x:term]])
  | _ => throw ()


@[app_unexpander Val.loc]
def unexpandValLoc: Unexpander
  | `($_ $x:num) => `([slf| $x:num])
  | `($_ $x:ident) => `([slf| [$x:ident]])
  | `($_ $x:term) => `([slf| [$x:term]])
  | _ => throw ()



@[app_unexpander Val.bool]
def unexpandValBool: Unexpander
  | `($_ $x:ident) =>
    match x with
    | `(true) => `([slf| true ])
    | `(false) => `([slf| false ])
    | _ => `([slf| [$x:ident]])
  | `($_ $x:term) => `([slf| [$x:term]])
  | _ => throw ()


@[app_unexpander Val.unit]
def unexpandValUnit: Unexpander
  | `($_) => `([slf| unit ])


@[app_unexpander Val.fun]
def unexpandValFun: Unexpander
  | `($_ $x:str [slf| $b]) =>
    let name := mkIdent (Lean.Name.mkStr1 x.getString)
    match b with
    | `(slf_term| fun $x* => $b) => `([slf| vfun $name $x* => $b ])
    | `(slf_term| $t ) => `([slf| vfun $name => $t ])
  | _ => throw ()


@[app_unexpander Val.fix]
def unexpandValFix: Unexpander
  | `($_ $f:str $x:str [slf| $b]) =>
    let name_f := mkIdent (Lean.Name.mkStr1 f.getString)
    let name_x := mkIdent (Lean.Name.mkStr1 x.getString)
    match b with
    | `(slf_term| fun $x* => $b) => `([slf| vfix $name_f $name_x $x* => $b ])
    | `(slf_term| $t ) => `([slf| vfix $name_f $name_x => $t ])
  | _ => throw ()


@[app_unexpander Val.prim]
def unexpandValPrim: Unexpander
  | `($_ $p) =>
    match p with
    | `(Prim.ref) => `([slf| ref ])
    | `(Prim.free) => `([slf| free ])
    | `(Prim.neg) => `([slf| not ])
    | `(Prim.rand) => `([slf| rand ])
    | _ => throw ()
  | _ => throw ()


@[app_unexpander Term.var]
def unexpandVar: Unexpander
  | `($_ $x:str) =>
    let name := mkIdent (Lean.Name.mkStr1 x.getString)
    `([slf| $name:ident ])
  | `($_ $x:term) => `([slf| [$x] ])
  | _ => throw ()


@[app_unexpander Term.val]
def unexpandVal: Unexpander
  | `($_ [slf| $n:num ]) => `([slf| $n:num])
  | `($_ $x:num) => `([slf| $x:num])
  | `($_ [slf| $x ]) => `([slf| $x ])
  | `($_ $x:term) => `([slf| [$x] ])
  | _ => throw ()


def addParen: TSyntax `slf_term → UnexpandM (TSyntax `slf_term)
  | `(slf_term| ($t) ) => `(slf_term| ($t))
  | t => `(slf_term| ($t))

def unexpandAppArg: TSyntax `slf_term → UnexpandM (TSyntax `slf_term)
  | `(slf_term| $f $x ) => `(slf_term| $f $x ) >>= addParen
  | t => `(slf_term| $t)

def unexpandAppFun: TSyntax `slf_term → UnexpandM (TSyntax `slf_term)
  | `(slf_term| $f $x ) => `(slf_term| $f $x)
  | `(slf_term| [$t] ) => `(slf_term| [$t])
  | `(slf_term| $i:ident ) => `(slf_term| $i:ident)
  | `(slf_term| ref ) => `(slf_term| ref)
  | `(slf_term| free ) => `(slf_term| free)
  | `(slf_term| not ) => `(slf_term| not)
  | `(slf_term| rand ) => `(slf_term| rand)
  | `(slf_term| ( $f ) ) => `(slf_term| ( $f ))
  | `(slf_term| $f ) => addParen f


def higherThanMul: TSyntax `slf_term → Bool
  | `(slf_term| unit ) => true
  | `(slf_term| $_:num ) => true
  | `(slf_term| $_:ident ) => true
  | `(slf_term| [ $_ ] ) => true
  | `(slf_term| ! $_ ) => true
  | _ => false


def wrapMulLeft: TSyntax `slf_term → UnexpandM (TSyntax `slf_term)
  | `(slf_term| $a * $b ) => `(slf_term| $a * $b)
  | `(slf_term| $a / $b ) => `(slf_term| $a / $b)
  | `(slf_term| $a % $b ) => `(slf_term| $a % $b)
  | t => addParen t


def higherThanAdd: TSyntax `slf_term → Bool
  | `(slf_term| - $_ ) => true
  | `(slf_term| $_ * $_ ) => true
  | `(slf_term| $_ / $_ ) => true
  | `(slf_term| $_ % $_ ) => true
  | t => higherThanMul t


def wrapAddLeft: TSyntax `slf_term → UnexpandM (TSyntax `slf_term)
  | `(slf_term| $a + $b ) => `(slf_term| $a + $b)
  | `(slf_term| $a - $b ) => `(slf_term| $a - $b)
  | t => addParen t


def higherThanPtrAdd: TSyntax `slf_term → Bool
  | `(slf_term| $_ + $_ ) => true
  | `(slf_term| $_ - $_ ) => true
  | t => higherThanAdd t


def wrapPtrAddLeft: TSyntax `slf_term → UnexpandM (TSyntax `slf_term)
  | `(slf_term| $a +> $b ) => `(slf_term| $a +> $b)
  | t => addParen t


def higherThanEq: TSyntax `slf_term → Bool
  | `(slf_term| $_ +> $_ ) => true
  | t => higherThanPtrAdd t


def higherThanLe: TSyntax `slf_term → Bool
  | `(slf_term| $_ == $_ ) => true
  | `(slf_term| $_ != $_ ) => true
  | t => higherThanEq t


@[app_unexpander Term.app]
def unexpandApp: Unexpander
  | `($_ [slf| $f] [slf| $a ]) => do
    let a' ← unexpandAppArg a
    let f' ← unexpandAppFun f
    let t ← `(slf_term|$f' $a')
    match t with
    -- unary operators
    | `(slf_term| [Val.prim Prim.get] $a) => `([slf| ! $a ])
    | `(slf_term| [Val.prim Prim.opp] $a) =>
      if higherThanMul a then `([slf| - $a ]) else `([slf| - ($a) ])
    | `(slf_term| ref $a) =>
      if higherThanMul a then `([slf| ref $a ]) else `([slf| ref ($a) ])
    | `(slf_term| free $a) =>
      if higherThanMul a then `([slf| free $a ]) else `([slf| free ($a) ])
    | `(slf_term| not $a) =>
      if higherThanMul a then `([slf| not $a ]) else `([slf| not ($a) ])
    | `(slf_term| rand $a) =>
      if higherThanMul a then `([slf| rand $a ]) else `([slf| rand ($a) ])
    -- binary operators
    | `(slf_term| [Val.prim Prim.set] $a:ident $b) => `([slf| $a:ident := $b ])
    | `(slf_term| [Val.prim Prim.set] [$t] $b) => `([slf| [$t] := $b ])
    | `(slf_term| [Val.prim Prim.ptr_add] $a $b) =>
      let a' ← if higherThanPtrAdd a then `(slf_term| $a) else wrapPtrAddLeft a
      let b' ← if higherThanPtrAdd b then `(slf_term| $b) else addParen b
      `([slf| $a' +> $b' ])
    | `(slf_term| [Val.prim Prim.add] $a $b) =>
      let a' ← if higherThanAdd a then `(slf_term| $a) else wrapAddLeft a
      let b' ← if higherThanAdd b then `(slf_term| $b) else addParen b
      `([slf| $a' + $b' ])
    | `(slf_term| [Val.prim Prim.sub] $a $b) =>
      let a' ← if higherThanAdd a then `(slf_term| $a) else wrapAddLeft a
      let b' ← if higherThanAdd b then `(slf_term| $b) else addParen b
      `([slf| $a' - $b' ])
    | `(slf_term| [Val.prim Prim.mul] $a $b) =>
      let a' ← if higherThanMul a then `(slf_term| $a) else wrapMulLeft a
      let b' ← if higherThanMul b then `(slf_term| $b) else addParen b
      `([slf| $a' * $b' ])
    | `(slf_term| [Val.prim Prim.div] $a $b) =>
      let a' ← if higherThanMul a then `(slf_term| $a) else wrapMulLeft a
      let b' ← if higherThanMul b then `(slf_term| $b) else addParen b
      `([slf| $a' / $b' ])
    | `(slf_term| [Val.prim Prim.mod] $a $b) =>
      let a' ← if higherThanMul a then `(slf_term| $a) else wrapMulLeft a
      let b' ← if higherThanMul b then `(slf_term| $b) else addParen b
      `([slf| $a' % $b' ])
    | `(slf_term| [Val.prim Prim.eq] $a $b) =>
      let a' ← if higherThanEq a then `(slf_term| $a) else addParen a
      let b' ← if higherThanEq b then `(slf_term| $b) else addParen b
      `([slf| $a' == $b' ])
    | `(slf_term| [Val.prim Prim.neq] $a $b) =>
      let a' ← if higherThanEq a then `(slf_term| $a) else addParen a
      let b' ← if higherThanEq b then `(slf_term| $b) else addParen b
      `([slf| $a' != $b' ])
    | `(slf_term| [Val.prim Prim.le] $a $b) =>
      let a' ← if higherThanLe a then `(slf_term| $a) else addParen a
      let b' ← if higherThanLe b then `(slf_term| $b) else addParen b
      `([slf| $a' <= $b' ])
    | `(slf_term| [Val.prim Prim.lt] $a $b) =>
      let a' ← if higherThanLe a then `(slf_term| $a) else addParen a
      let b' ← if higherThanLe b then `(slf_term| $b) else addParen b
      `([slf| $a' < $b' ])
    | `(slf_term| [Val.prim Prim.ge] $a $b) =>
      let a' ← if higherThanLe a then `(slf_term| $a) else addParen a
      let b' ← if higherThanLe b then `(slf_term| $b) else addParen b
      `([slf| $a' >= $b' ])
    | `(slf_term| [Val.prim Prim.gt] $a $b) =>
      let a' ← if higherThanLe a then `(slf_term| $a) else addParen a
      let b' ← if higherThanLe b then `(slf_term| $b) else addParen b
      `([slf| $a' > $b' ])
    | t => `([slf| $t ])
  | _ => throw ()


@[app_unexpander Term.if]
def unexpandIf: Unexpander
  | `($_ [slf| $cond] [slf| $t] [slf| $f]) =>
    match f with
    | `(slf_term| unit ) => `([slf| if $cond then $t end ])
    | `(slf_term| $f) => `([slf| if $cond then $t else $f ])
  | _ => throw ()


@[app_unexpander Term.seq]
def unexpandSeq: Unexpander
  | `($_ [slf| $a] [slf| $b ]) => `([slf| $a; $b ])
  | _ => throw ()


@[app_unexpander Term.fun]
def unexpandFun: Unexpander
  | `($_ $x:str $a) =>
    let name := mkIdent (Lean.Name.mkStr1 x.getString)
    match a with
    | `([slf| fun $x* => $a ]) => `([slf| fun $name $x* => $a ])
    | `([slf| $t ]) => `([slf| fun $name => $t ])
    | _ => throw ()
  | _ => throw ()


@[app_unexpander Term.fix]
def unexpandFix: Unexpander
  | `($_ $f:str $x:str $a) =>
    let name_f := mkIdent (Lean.Name.mkStr1 f.getString)
    let name_x := mkIdent (Lean.Name.mkStr1 x.getString)
    match a with
    | `([slf| fun $x* => $a ]) => `([slf| fix $name_f $name_x $x* => $a ])
    | `([slf| $t ]) => `([slf| fix $name_f $name_x => $t ])
    | _ => throw ()
  | _ => throw ()


@[app_unexpander Term.let]
def unexpandLet: Unexpander
  | `($_ $x:str [slf| $v ] [slf| $b ]) =>
    let name := mkIdent (Lean.Name.mkStr1 x.getString)
    match v with
    | `(slf_term| fun $x* => $v ) => `([slf| let $name $x* := $v in $b ])
    | `(slf_term| fix $_ $x* => $v ) => `([slf| let rec $name $x* := $v in $b ])
    | `(slf_term| $v ) => `([slf| let $name := $v in $b ])
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

def i: Int := 3
def b: Bool := true
def num: Val := 3
def x: String := "x"
def l: Loc := 3

-- values
-- integer values
#guard slf_pp Val.int 3 = "[slf| 3 ]"
#guard slf_pp [slf| [Val.int 3]] = "[slf| 3 ]"
#guard slf_pp [slf| [Val.int i] ] = "[slf| [i] ]"
#guard slf_pp [slf| 3] = "[slf| 3 ]"
#guard slf_pp [slf| [3]] = "3"  -- ofNat is just a `3`
#guard slf_pp ([slf| 3] : Term) = "[slf| 3 ]"
#guard slf_pp Term.val num = "[slf| [num] ]"
-- boolean values
#guard slf_pp Val.bool true = "[slf| true ]"
#guard slf_pp [slf| true] = "[slf| true ]"
#guard slf_pp ([slf| true]: Term) = "[slf| true ]"
#guard slf_pp Val.bool b = "[slf| [b] ]"
#guard slf_pp [slf| [b == b]] = "[slf| [b == b] ]"
-- unit value
#guard slf_pp Val.unit = "[slf| unit ]"
#guard slf_pp Term.val Val.unit = "[slf| unit ]"
#guard slf_pp [slf| unit] = "[slf| unit ]"
#guard slf_pp ([slf| unit]: Term) = "[slf| unit ]"
-- function values
#guard slf_pp Val.fun "x" [slf| x] = "[slf| vfun x => x ]"
#guard slf_pp [slf| vfun a => b] = "[slf| vfun a => b ]"
#guard slf_pp ([slf| vfun a => b]: Term) = "[slf| vfun a => b ]"
#guard slf_pp [slf| vfun x => fun y => fun z => z] = "[slf| vfun x y z => z ]"
#guard slf_pp Val.fix "f" "x" [slf| x] = "[slf| vfix f x => x ]"
#guard slf_pp [slf| vfix f a => b] = "[slf| vfix f a => b ]"
#guard slf_pp ([slf| vfix f a => b]: Term) = "[slf| vfix f a => b ]"
#guard slf_pp [slf| vfix f a => fun b => c] = "[slf| vfix f a b => c ]"

-- terms
#guard slf_pp Term.var x = "[slf| [x] ]"
#guard slf_pp [slf| x] = "[slf| x ]"
#guard slf_pp [slf| ["x"]] = "[slf| x ]"
#guard slf_pp [slf| [x ++ "y"] y z] = "[slf| [x ++ \"y\"] y z ]"
#guard slf_pp [slf| (x y) z] = "[slf| x y z ]"
#guard slf_pp [slf| x (y z)] = "[slf| x (y z) ]"
#guard slf_pp [slf| x (y (z w))] = "[slf| x (y (z w) ) ]"
#guard slf_pp [slf| x (y z) w] = "[slf| x (y z) w ]"
#guard slf_pp [slf| x y z w] = "[slf| x y z w ]"
#guard slf_pp [slf| [x] y z w] = "[slf| [x] y z w ]"
#guard slf_pp [slf| [x] y [x] w] = "[slf| [x] y [x] w ]"
#guard slf_pp [slf| [x] (y [x]) w] = "[slf| [x] (y [x] ) w ]"
#guard slf_pp [slf| if x then y else z] = "[slf| if x then y else z ]"
#guard slf_pp [slf| if x then y end] = "[slf| if x then y end ]"
#guard slf_pp [slf| if [x] then y; z else w] = "[slf| if [x] then y; z else w ]"
#guard slf_pp [slf| (fun x => x y) z] = "[slf| (fun x => x y) z ]"
#guard slf_pp [slf| fun x => (x y z)] = "[slf| fun x => x y z ]"
#guard slf_pp [slf| fun x => fun y => fun z => z] = "[slf| fun x y z => z ]"
#guard slf_pp [slf| (fun x y => fun z => z) w] = "[slf| (fun x y z => z) w ]"
#guard slf_pp [slf| if [x] then y; z else w] = "[slf| if [x] then y; z else w ]"
#guard slf_pp [slf| (if [x] then y; z else w) c] = "[slf| (if [x] then y; z else w) c ]"
#guard slf_pp [slf| (fix f x => x y) z] = "[slf| (fix f x => x y) z ]"
#guard slf_pp [slf| (fix f x y => x y) z] = "[slf| (fix f x y => x y) z ]"
#guard slf_pp [slf| (fix f x y z => x y) z] = "[slf| (fix f x y z => x y) z ]"
#guard slf_pp [slf| (fix f x => fun y => fun z => x y) z] = "[slf| (fix f x y z => x y) z ]"
#guard slf_pp [slf| (fix f x => fun y => fun z => x y) z] = "[slf| (fix f x y z => x y) z ]"
#guard slf_pp [slf| (fix f x => fun y => if x then y; fun z => x y else z) z] = "[slf| (fix f x y => if x then y; fun z => x y else z) z ]"
-- let rules
#guard slf_pp [slf| let x := y in z] = "[slf| let x := y in z ]"
#guard slf_pp [slf| let x y := z in w] = "[slf| let x y := z in w ]"
#guard slf_pp [slf| let rec f x := y in z] = "[slf| let rec f x := y in z ]"
#guard slf_pp [slf| let rec f x y := z in w] = "[slf| let rec f x y := z in w ]"
#guard slf_pp [slf| let rec f x y := z in [x] w] = "[slf| let rec f x y := z in [x] w ]"
-- primitives
-- `ref`, `free`, `not` are printed as is
def prim := Val.prim Prim.get
#guard slf_pp prim = "prim"
#guard slf_pp [slf| [prim]] = "[slf| [prim] ]"
#guard slf_pp [slf| ref] = "[slf| ref ]"
#guard slf_pp [slf| ref x] = "[slf| ref x ]"
#guard slf_pp [slf| free] = "[slf| free ]"
#guard slf_pp [slf| free x] = "[slf| free x ]"
#guard slf_pp [slf| free (x + 1)] = "[slf| free (x + 1) ]"
#guard slf_pp [slf| (free x) + 1] = "[slf| (free x) + 1 ]"
#guard slf_pp [slf| free x + 1] = "[slf| (free x) + 1 ]"
#guard slf_pp [slf| not] = "[slf| not ]"
-- the rest must be application of the primitive to its arguments
-- get
#guard slf_pp (Term.app (Val.prim Prim.get) x) = "[slf| ! [x] ]"
#guard slf_pp [slf| !x] = "[slf| !x ]"
#guard slf_pp [slf| !!x] = "[slf| !!x ]"
#guard slf_pp [slf| ! x (x y)] = "[slf| ! (x (x y) ) ]"
#guard slf_pp [slf| ! x x y] = "[slf| ! (x x y) ]"
-- assign
#guard slf_pp (Term.app (Term.app (Val.prim Prim.set) x) "y") = "[slf| [x] := y ]"
-- arithmetic
#guard slf_pp (Term.app (Term.app (Val.prim Prim.add) x) "y") = "[slf| [x] + y ]"
#guard slf_pp [slf| [num] + y ] = "[slf| [num] + y ]"
#guard slf_pp [slf| [num] + [num] ] = "[slf| [num] + [num] ]"
#guard slf_pp [slf| [num] + [i] ] = "[slf| [num] + [i] ]"
-- #guard slf_pp [slf| [3] + [i] ] = "[slf| 3 + [i] ]"
#guard slf_pp (Term.val (.int (i + i))) = "[slf| [i + i] ]"
#guard slf_pp [slf| [i + i] ] = "[slf| [i + i] ]"
#guard slf_pp [slf| (x := y) + y] = "[slf| (x := y) + y ]"
#guard slf_pp [slf| (x + y) + z] = "[slf| x + y + z ]"
#guard slf_pp [slf| x + (y + z)] = "[slf| x + (y + z) ]"
#guard slf_pp [slf| x - (y + z)] = "[slf| x - (y + z) ]"
#guard slf_pp [slf| x - y - z] = "[slf| x - y - z ]"
#guard slf_pp [slf| x - -y - z] = "[slf| x - -y - z ]"
#guard slf_pp [slf| x * (y * z)] = "[slf| x * (y * z) ]"
#guard slf_pp [slf| x * y * z] = "[slf| x * y * z ]"
#guard slf_pp [slf| x * (y + z)] = "[slf| x * (y + z) ]"
#guard slf_pp [slf| x * y + z] = "[slf| x * y + z ]"
#guard slf_pp [slf| x * (-y) + z] = "[slf| x * (-y) + z ]"
#guard slf_pp [slf| -x * y + z] = "[slf| - (x * y) + z ]"
#guard slf_pp [slf| (-x) * y + z] = "[slf| (-x) * y + z ]"
-- pointer arithmetic
#guard slf_pp [slf| x +> y +> z] = "[slf| x +> y +> z ]"
#guard slf_pp [slf| x +> y * z] = "[slf| x +> y * z ]"
#guard slf_pp [slf| x +> y + z] = "[slf| x +> y + z ]"
#guard slf_pp [slf| x +> y + z +> 5 * w % 3] = "[slf| x +> y + z +> 5 * w % 3 ]"
#guard slf_pp [slf| [l] +> y] = "[slf| [l] +> y ]"
#guard slf_pp [slf| [l] +> 3] = "[slf| [l] +> 3 ]"
#guard slf_pp [slf| 3 +> y] = "[slf| 3 +> y ]"
-- comparison
#guard slf_pp [slf| -x + y == z] = "[slf| -x + y == z ]"
#guard slf_pp [slf| -x + (y != z)] = "[slf| -x + (y != z) ]"
#guard slf_pp [slf| -x + (y <= z)] = "[slf| -x + (y <= z) ]"
#guard slf_pp [slf| -x + (y < z)] = "[slf| -x + (y < z) ]"
#guard slf_pp [slf| -[x] + (y >= z)] = "[slf| - [x] + (y >= z) ]"
#guard slf_pp [slf| [num] + (y >= z)] = "[slf| [num] + (y >= z) ]"
#guard slf_pp [slf| (x := 3) <= (y > z)] = "[slf| (x := 3) <= (y > z) ]"
#guard slf_pp [slf| x +> 3 == y] = "[slf| x +> 3 == y ]"
