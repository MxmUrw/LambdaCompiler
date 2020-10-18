
module Base.List where

open import Base.Imports

List-++-[] : {ℓ : ULevel} {A : 𝒰 ℓ} -> (v : List A) -> v ++ ([]) == v
List-++-[] [] = refl
List-++-[] (x :: v) = cong (x ::_) (List-++-[] v)

