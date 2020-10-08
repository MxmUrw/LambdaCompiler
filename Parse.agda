module Parse where

import Ast
open import Data.Nat using (ℕ; _+_; _*_; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Char using (Char; _==_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String; toList)


-- does this exist in the stdlib?
unwrap-or : {T : Set} -> Maybe T -> T -> T
unwrap-or (just x) _ = x
unwrap-or nothing fallback = fallback

pow : ℕ -> ℕ -> ℕ
pow x 0 = 1
pow x (suc exp) = x * pow x exp

len : {T : Set} -> List T -> ℕ
len [] = 0
len (x ∷ l) = suc (len l)
----------------------------------

Str = List Char

record ParserResult (T : Set) : Set where
  field value : T
  field remaining : Str

Parser : (A : Set) -> Set
Parser x = Str -> Maybe (ParserResult x)

parse-str : Str -> Parser ⊤
parse-str [] payload = just (record { value = tt; remaining = payload })
parse-str (x ∷ _) [] = nothing
parse-str (x ∷ pat) (y ∷ payload) with x == y
... | true = parse-str pat payload
... | false = nothing

parse-string : String -> Parser ⊤
parse-string x = parse-str (toList x) -- TODO use . instead, when I know where to import it from

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

parse-digit-seq : Str -> ParserResult (List ℕ)
parse-digit-seq [] = record { value = []; remaining = [] }
parse-digit-seq (c ∷ xs) = unwrap-or (Data.Maybe.map (λ x -> let rest = parse-digit-seq xs in record { value = x ∷ ParserResult.value rest; remaining = ParserResult.remaining rest }) (char→ℕ c)) record { value = []; remaining = (c ∷ xs) } -- well, this is kinda ugly

parse-ℕ-helper : List ℕ -> Maybe ℕ
parse-ℕ-helper [] = nothing
parse-ℕ-helper (x ∷ xs) = just (x * (pow 10 (len xs)) + (unwrap-or (parse-ℕ-helper xs) 0))

parse-ℕ : Parser ℕ
parse-ℕ x = (λ a -> Data.Maybe.map (λ b -> record { value = b; remaining = ParserResult.remaining a}) (parse-ℕ-helper (ParserResult.value a))) (parse-digit-seq x)

{-
parse-term : Parser Ast.Term
parse-term = {!!}

parse-main : Parser Ast.Item
parse-main = (parse-string "main(", parse-num, parse-string ") := ", parse-term)

parse-let : Parser Ast.Item
parse-let = {!!}


parse-impl : List Ast.Item -> Parser Ast.Program
parse-impl x = {!!}

parse : Parser Ast.Program
parse = parse-impl []

-}
