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
pow : ℕ -> ℕ -> ℕ
pow x 0 = 1
pow x (suc y) = x * pow x y

len : {T : Set} -> List T -> ℕ
len [] = 0
len (x ∷ l) = suc (len l)

_unwrap-or_ : {T : Set} -> Maybe T -> T -> T
_unwrap-or_ (just x) _ = x
_unwrap-or_ nothing fallback = fallback

_M-map_ : {T U : Set} -> Maybe T -> (T -> U) -> Maybe U
nothing M-map _ = nothing
just x M-map f = just (f x)

_or_ : {T : Set} -> Maybe T -> Maybe T -> Maybe T
_or_ (just x) _ = just x
_or_ nothing y = y
infixl 30 _or_

append : {T : Set} -> List T -> T -> List T
append [] y = y ∷ []
append (x ∷ l) y = x ∷ (append l y)

rev : {T : Set} -> List T -> List T
rev [] = []
rev (x ∷ l) = append (rev l) x

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
  QuestionMark : Token

data CharInfo : Set where
  sign : Token -> CharInfo
  ident : Char -> CharInfo
  digit : ℕ -> CharInfo
  space : CharInfo
  err : CharInfo

data TokenizerState : Set where
  ts-Default : TokenizerState
  ts-Ident : Str -> TokenizerState
  ts-Nat : List ℕ -> TokenizerState

-- ident-token
ident-info-helper : Char -> Bool -> Maybe CharInfo
ident-info-helper c true = just (ident c)
ident-info-helper c false = nothing

ident-info : Char -> Maybe CharInfo
ident-info c = ident-info-helper c (is-ident c)
----

-- nat-token
nat-info-helper : Maybe ℕ -> Maybe CharInfo
nat-info-helper = Data.Maybe.map digit

nat-info : Char -> Maybe CharInfo
nat-info c = nat-info-helper (char→ℕ c)
----

-- sign-token
sign-info : Char -> Maybe CharInfo
sign-info '(' = just (sign ParenL)
sign-info ')' = just (sign ParenR)
sign-info '\\' = just (sign Backslash)
sign-info '.' = just (sign Dot)
sign-info '?' = just (sign QuestionMark)
sign-info _ = nothing
----

-- space-token
space-info : Char -> Maybe CharInfo
space-info ' ' = just space
space-info '\n' = just space
space-info '\t' = just space
space-info _ = nothing
--

char-info : Char -> CharInfo
char-info c = ((ident-info c) or (nat-info c) or (sign-info c) or (space-info c)) unwrap-or err

-- tokenize
{-# TERMINATING #-}
tokenize-stack : Str -> Maybe (List Token)
{-# TERMINATING #-}
tokenize-impl : Str -> TokenizerState -> Maybe (List Token)
{-# TERMINATING #-}
tokenize-impl2 : CharInfo -> Str -> TokenizerState -> Maybe (List Token)

digits-to-nat : List ℕ -> ℕ
digits-to-nat [] = 0
digits-to-nat (x ∷ l) = (digits-to-nat l) + (x * (pow 10 (len l)))

on-back-default : TokenizerState -> Maybe Token
on-back-default ts-Default = nothing
on-back-default (ts-Ident x) = just (Ident x)
on-back-default (ts-Nat x) = just (Nat (digits-to-nat x))

on-back-default-usage-helper : List Token -> Maybe Token -> List Token
on-back-default-usage-helper l nothing = l
on-back-default-usage-helper l (just x) = x ∷ l

on-back-default-usage : TokenizerState -> List Token -> List Token
on-back-default-usage ts l = on-back-default-usage-helper l (on-back-default ts)

 -- ident & digit proceed
tokenize-impl2 (ident c) str (ts-Ident xs) = tokenize-impl str (ts-Ident (c ∷ xs))
tokenize-impl2 (digit d) str (ts-Nat xs) = tokenize-impl str (ts-Nat (d ∷ xs))

 -- default
tokenize-impl2 (sign x) str ts-Default = (tokenize-stack str) M-map (λ l -> x ∷ l)
tokenize-impl2 (ident x) str ts-Default = tokenize-impl str (ts-Ident (x ∷ []))
tokenize-impl2 (digit x) str ts-Default = tokenize-impl str (ts-Nat (x ∷ []))
tokenize-impl2 space str ts-Default = tokenize-impl str ts-Default
tokenize-impl2 err str ts-Default = nothing

 -- ident & digit end
tokenize-impl2 ci str ts = (tokenize-impl2 ci str ts-Default) M-map (on-back-default-usage ts)

tokenize-impl [] ts = just (on-back-default-usage ts [])
tokenize-impl (c ∷ str) = tokenize-impl2 (char-info c) str

tokenize-stack s = tokenize-impl s ts-Default

tokenize : Str -> Maybe (List Token)
tokenize s = tokenize-stack s M-map rev
----
