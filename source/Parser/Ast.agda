module Parser.Ast where

open import Data.List using (List)
open import Data.String using (String)
open import Data.Nat using (ℕ)

Arity = ℕ

data Term : Set where
  Abstraction : String -> Term -> Term
  Apply : Term -> Term -> Term
  Var : String -> Term
  Nat : ℕ -> Term -- number literal
  InputVar : ℕ -> Term -- CLI argument
