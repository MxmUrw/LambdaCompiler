module Parser.Token where

open import Data.Nat using (ℕ; _+_; _*_; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Char using (Char; _==_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String; toList)
open import Foreign.Haskell.Pair using (Pair; _,_)


-- does this exist in the stdlib?
unwrap-or : {T : Set} -> Maybe T -> T -> T
unwrap-or (just x) _ = x
unwrap-or nothing fallback = fallback

_or_ : {T : Set} -> Maybe T -> Maybe T -> Maybe T
_or_ (just x) _ = just x
_or_ nothing y = y
infixl 30 _or_

Str = List Char

char→ℕ : Char -> Maybe ℕ
char→ℕ '0' = just 0
char→ℕ '1' = just 1
char→ℕ '2' = just 2
char→ℕ '3' = just 3
char→ℕ '4' = just 4
char→ℕ '5' = just 5
char→ℕ '6' = just 6
char→ℕ '7' = just 7
char→ℕ '8' = just 8
char→ℕ '9' = just 9
char→ℕ _ = nothing

is-ident : Char -> Bool
is-ident = Data.Char.isAlpha

data Token : Set where
  Ident : Str -> Token
  Nat : ℕ -> Token
  ParenL : Token
  ParenR : Token
  Backslash : Token
  Dot : Token
  Equals : Token

TokenOrSpace = Maybe Token
ErrorOr : (T : Set) -> Set
ErrorOr x = Maybe x

data TokenizerState : Set where
  ts-Default : TokenizerState
  ts-Ident : Str -> TokenizerState
  ts-Nat : List ℕ -> TokenizerState

-- ident-token
ident-token-helper : Char -> Bool -> Maybe Token
ident-token-helper c true = just (Ident (c ∷ []))
ident-token-helper c false = nothing

ident-token : Char -> Maybe Token
ident-token c = ident-token-helper c (is-ident c)
----

-- nat-token
nat-token-helper : Char -> Maybe ℕ -> Maybe Token
nat-token-helper _ = Data.Maybe.map Nat

nat-token : Char -> Maybe Token
nat-token c = nat-token-helper c (char→ℕ c)
----

-- sign-token
sign-token : Char -> Maybe Token
sign-token '(' = just ParenL
sign-token ')' = just ParenR
sign-token '\\' = just Backslash
sign-token '.' = just Dot
sign-token '=' = just Equals
sign-token _ = nothing
----

tokenize-nonspace-char : Char -> Maybe Token
tokenize-nonspace-char c = (ident-token c) or (nat-token c) or (sign-token c)

tokenize-char : Char -> ErrorOr TokenOrSpace
tokenize-char ' ' = just nothing
tokenize-char c = Data.Maybe.map just (tokenize-nonspace-char c)

tokenize-impl2 : Token -> Str -> TokenizerState -> Maybe (List Token)
tokenize-impl2 t str ts-Default = {!!}
tokenize-impl2 t str (ts-Ident x) = {!!}
tokenize-impl2 t str (ts-Nat x) = {!!}

tokenize-impl : Str -> TokenizerState -> Maybe (List Token)
tokenize-impl [] ts = {!!}
-- tokenize-impl (c ∷ str) ts = Data.Maybe.map (λ mt -> unwrap-or (Data.Maybe.map (λ t -> tokenize-impl2 t str ts) mt) []) (tokenize-char c)

tokenize : Str -> Maybe (List Token)
tokenize s = tokenize-impl s ts-Default
