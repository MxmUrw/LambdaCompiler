module Parser.Ast where

open import Data.List using (List)
open import Data.Char using (Char)
open import Data.String using (String)
open import Data.Nat using (ℕ)

Arity = ℕ

Str = List Char

data Term : Set where
  Abstraction : Str -> Term -> Term
  Apply : Term -> Term -> Term
  Var : Str -> Term
  Nat : ℕ -> Term -- number literal
  InputVar : ℕ -> Term -- CLI argument
