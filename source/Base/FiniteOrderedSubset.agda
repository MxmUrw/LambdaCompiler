
module Base.FiniteOrderedSubset where

open import Base.Imports
open import Base.List

data _⊆_ {A : 𝒰 ℓ} : (S T : List A) -> 𝒰 ℓ where
  refl : ∀{S} -> S ⊆ S
  skip : ∀{S T a} -> S ⊆ T -> S ⊆ (T ,, a)
  next : ∀{S T a} -> S ⊆ T -> (S ,, a) ⊆ (T ,, a)

trans-∈-⊆ : ∀{A : 𝒰 ℓ} -> {a : A} -> {v w : List A} -> (a ∈ v) -> (v ⊆ w) -> a ∈ w
trans-∈-⊆ a refl = a
trans-∈-⊆ a (skip b) = next (trans-∈-⊆ a b)
trans-∈-⊆ this (next b) = this
trans-∈-⊆ (next a) (next b) = next (trans-∈-⊆ a b)

trans-⊆ : ∀{A : 𝒰 ℓ} -> {u v w : List A} -> (u ⊆ v) -> (v ⊆ w) -> u ⊆ w
trans-⊆ a refl = a
trans-⊆ a (skip b) = skip (trans-⊆ a b)
trans-⊆ refl (next b) = next b
trans-⊆ (skip a) (next b) = skip (trans-⊆ a b)
trans-⊆ (next a) (next b) = next (trans-⊆ a b)

initial-⊆ : ∀{A : 𝒰 ℓ} {u : List A} -> [] ⊆ u
initial-⊆ {u = []} = refl
initial-⊆ {u = x :: u} = skip initial-⊆

++→⊆-l : ∀{A : 𝒰 ℓ} -> (u : List A) -> {v : List A} -> v ⊆ (u ++ v)
++→⊆-l [] {v} = refl
++→⊆-l (x :: u) {v} = skip (++→⊆-l _)

++→⊆-r : ∀{A : 𝒰 ℓ} -> (u : List A) -> {v : List A} -> v ⊆ (v ++ u)
++→⊆-r u {[]} = initial-⊆
++→⊆-r u {x :: v} = next (++→⊆-r _)
