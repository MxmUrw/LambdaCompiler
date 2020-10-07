module Parse where

import Ast
open import Data.List using ([])
open import Data.String using (String)
open import Foreign.Haskell.Either using (Either; right)

Err = String

parse : String -> Either Ast.Program Err
parse x = right "unimplemented"
