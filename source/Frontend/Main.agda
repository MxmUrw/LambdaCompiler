
module Frontend.Main where

open import Data.Unit.Polymorphic
open import Codata.Musical.Notation
open import Codata.Musical.Colist
open import Codata.Musical.Costring
open import IO

open import Frontend.ExampleImport

main : _
main = run (♯ (putStrLn (myText)) >>= (λ _ -> ♯ return tt))



