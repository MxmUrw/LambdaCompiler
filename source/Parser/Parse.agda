module Parser.Parse where

open import Parser.Ast using (Term; Str)
open import Parser.Token using (Token; tokenize; _unwrap-or_; _or_; _M-map_)
open import Data.Nat using (ℕ; _+_; _*_; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Char using (Char; _==_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String; toList)
open import Foreign.Haskell.Pair using (Pair; _,_)
open import Function using (_∘_)

data ParserResult (T : Set) : Set where
  success : T -> List Token -> ParserResult T
  error : ParserResult T

Parser : (A : Set) -> Set
Parser x = List Token -> ParserResult x

_PR-map_ : {T Out : Set} -> ParserResult T -> (T -> Out) -> ParserResult Out
success value remaining PR-map f = success (f value) remaining
error                   PR-map _ = error

_PR-or_ : {T : Set} -> ParserResult T -> ParserResult T -> ParserResult T
success value remaining PR-or _ = success value remaining
error                   PR-or y = y
infixl 30 _PR-or_

_P-or_ : {T : Set} -> Parser T -> Parser T -> Parser T
_P-or_ p1 p2 l = (p1 l) PR-or (p2 l) -- if this is not evaluated laziliy, this will have terrible performance!
infixl 30 _P-or_

_M-and-then_ : {T U : Set} -> Maybe T -> (T -> Maybe U) -> Maybe U
nothing M-and-then _ = nothing
just x M-and-then f = f x

{-# TERMINATING #-}
parse-one : Parser Term
{-# TERMINATING #-}
parse-max : Parser Term

-- parse-paren
parse-paren-helper : ParserResult Term -> ParserResult Term
parse-paren-helper (success t (Token.ParenR ∷ l)) = success t l
parse-paren-helper _ = error

parse-paren : Parser Term
parse-paren (Token.ParenL ∷ l) = parse-paren-helper (parse-max l)
parse-paren _ = error
----

-- parse-abstr
parse-abstr : Parser Term
parse-abstr (Token.Backslash ∷ Token.Ident i ∷ Token.Dot ∷ l) = (parse-max l) PR-map (Term.Abstraction i)
parse-abstr _ = error
----

-- parse-atom
parse-atom : Parser Term
parse-atom (Token.Ident i ∷ l) = success (Term.Var i) l
parse-atom (Token.Nat n ∷ l) = success (Term.Nat n) l
parse-atom (Token.QuestionMark ∷ Token.Nat n ∷ l) = success (Term.InputVar n) l
parse-atom _ = error
----

parse-one = parse-paren P-or parse-abstr P-or parse-atom

-- parse-max

loop : Term -> List Token -> ParserResult Term
loop-helper : Term -> List Token -> ParserResult Term -> ParserResult Term

loop-helper t1 _ (success t2 l) = loop (Term.Apply t1 t2) l
loop-helper t1 orig error = success t1 orig

loop t [] = success t []
loop t l = (loop-helper t l) (parse-one l)

parse-max-helper : ParserResult Term -> ParserResult Term
parse-max-helper (success t1 l) = loop t1 l
parse-max-helper error = error

parse-max = parse-max-helper ∘ parse-one
----


PR-to-maybe : {T : Set} -> ParserResult T -> Maybe T
PR-to-maybe (success x []) = just x
PR-to-maybe _ = nothing

parse-tokens : List Token -> Maybe Term
parse-tokens = PR-to-maybe ∘ parse-max

parse : Str -> Maybe Term
parse x = (tokenize x) M-and-then parse-tokens

parse-example = parse (toList "(\\xy. + xy ?0) (foo ?12 3)")
-- run Space m n
