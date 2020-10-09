module Parser.Parse where

import Parser.Ast as Ast
open import Parser.Token using (Token; Str; tokenize; unwrap-or)
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
pow x (suc exp) = x * pow x exp

len : {T : Set} -> List T -> ℕ
len [] = 0
len (x ∷ l) = suc (len l)

and : {T1 T2 : Set} -> Maybe T1 -> Maybe T2 -> Maybe (Pair T1 T2)
and {T1} {T2} nothing nothing = nothing
and {T1} {T2} nothing (just y) = nothing
and {T1} {T2} (just x) nothing = nothing
and {T1} {T2} (just x) (just y) = just (x , y)
----------------------------------

record ParserResult (T : Set) : Set where
  field value : T
  field remaining : Str

Parser : (A : Set) -> Set
Parser x = Str -> Maybe (ParserResult x)

ParserResult-map : {T Out : Set} -> (T -> Out) -> ParserResult T -> ParserResult Out
ParserResult-map {T} {Out} f r = record { value = f (ParserResult.value r); remaining = ParserResult.remaining r}

Maybe-ParserResult-map : {T Out : Set} -> (T -> Out) -> Maybe (ParserResult T) -> Maybe (ParserResult Out)
Maybe-ParserResult-map {T} {Out} f = Data.Maybe.map (ParserResult-map f)

apply : {T1 T2 : Set} -> ParserResult T1 -> Parser T2 -> Maybe (ParserResult (Pair T1 T2))
apply {T1} {T2} r p = Maybe-ParserResult-map (λ x -> ParserResult.value r , x) (p (ParserResult.remaining r))

apply-maybe : {T1 T2 : Set} -> Maybe (ParserResult T1) -> Parser T2 -> Maybe (ParserResult (Pair T1 T2))
apply-maybe nothing _ = nothing
apply-maybe (just x) = apply x


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
parse-digit-seq (c ∷ xs) = unwrap-or (Data.Maybe.map (λ x -> let rest = parse-digit-seq xs in record { value = x ∷ ParserResult.value rest; remaining = ParserResult.remaining rest }) (char→ℕ c)) record { value = []; remaining = (c ∷ xs) } -- well, this is kinda ugly, I should use ParserResult-map

parse-ℕ-helper : List ℕ -> Maybe ℕ
parse-ℕ-helper [] = nothing
parse-ℕ-helper (x ∷ xs) = just (x * (pow 10 (len xs)) + (unwrap-or (parse-ℕ-helper xs) 0))

parse-ℕ : Parser ℕ
parse-ℕ x = (λ a -> Data.Maybe.map (λ b -> record { value = b; remaining = ParserResult.remaining a}) (parse-ℕ-helper (ParserResult.value a))) (parse-digit-seq x) -- I should use ParserResult-map

parse-2 : {T1 T2 Out : Set} -> Parser T1 -> Parser T2 -> (T1 -> T2 -> Out) -> Parser Out
parse-2 {T1} {T2} {Out} p1 p2 f str = Data.Maybe.map (ParserResult-map (λ x -> f (Pair.fst x) (Pair.snd x))) (apply-maybe (p1 str) p2)

-- would be nice to generalise this using variadic generics; Is this possible?
parse-3 : {T1 T2 T3 Out : Set} -> Parser T1 -> Parser T2 -> Parser T3 -> (T1 -> T2 -> T3 -> Out) -> Parser Out
parse-3 {T1} {T2} {T3} {Out} p1 p2 p3 f =
                                    let p12 = (parse-2 {T1} {T2} {Pair T1 T2} p1 p2 (λ x y -> x , y)) in
                                    parse-2 p12 p3 (λ pair v3 -> f (Pair.fst pair) (Pair.snd pair) v3)


parse-4 : {T1 T2 T3 T4 Out : Set} -> Parser T1 -> Parser T2 -> Parser T3 -> Parser T4 -> (T1 -> T2 -> T3 -> T4 -> Out) -> Parser Out
parse-4 {T1} {T2} {T3} {T4} {Out} p1 p2 p3 p4 f =
                                        let p12 = (parse-2 {T1} {T2} {Pair T1 T2} p1 p2 (_,_)) in
                                        let p34 = (parse-2 {T3} {T4} {Pair T3 T4} p3 p4 (_,_)) in
                                                  parse-2 p12 p34 (λ pair12 pair34 -> f (Pair.fst pair12) (Pair.snd pair12) (Pair.fst pair34) (Pair.snd pair34))

parse-term : Parser Ast.Term
parse-term = {!!}

parse-main : Parser Ast.Item
parse-main = parse-4 (parse-string "main(") parse-ℕ (parse-string ") := ") parse-term (λ _ arity _ term -> Ast.Main arity term)

{-


parse-let : Parser Ast.Item
parse-let = {!!}


parse-impl : List Ast.Item -> Parser Ast.Program
parse-impl x = {!!}

parse : Parser Ast.Program
parse = parse-impl []

-}
