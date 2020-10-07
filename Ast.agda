module Ast where

open import Agda.Builtin.Bool public
open import Agda.Builtin.List public
open import Agda.Builtin.String public
open import Agda.Builtin.Nat public

Arity = Nat

data Term : Set where
  Abstraction : String -> Term -> Term
  Apply : Term -> Term -> Term
  Var : String -> Term
  Int : Nat -> Term


data Item : Set where
  Let : String -> Term -> Item
  Main : Arity -> Term -> Item

Program = List Item

