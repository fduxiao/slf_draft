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


def heap := FMap Loc Val
