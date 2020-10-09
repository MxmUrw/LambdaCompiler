module Parser.Ast where

open import Data.List using (List)
open import Data.String using (String)
open import Data.Nat using (ℕ)

Arity = ℕ

data Term : Set where
  Abstraction : String -> Term -> Term
  Apply : Term -> Term -> Term
  Var : String -> Term
  Int : ℕ -> Term


data Item : Set where
  Let : String -> Term -> Item
  Main : Arity -> Term -> Item

Program = List Item

