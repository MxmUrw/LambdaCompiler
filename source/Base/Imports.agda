
module Base.Imports where

-------------------------------
-- Universes and equality

open import Agda.Primitive renaming (Level to ULevel ; lsuc to _⁺) public
open import Agda.Builtin.Equality public using (refl) renaming (_≡_ to _==_)

variable
  ℓ : ULevel
  ℓ' : ULevel
  ℓ'' : ULevel
  𝑖 𝑗 𝑘 𝑙 : ULevel

ℓ₀ = lzero
ℓ₁ = ℓ₀ ⁺

𝒰 : (i : ULevel) -> Set (i ⁺)
𝒰 i = Set i

𝒰₀ = 𝒰 ℓ₀
𝒰₁ = 𝒰 ℓ₁

-------------------------------
-- List
open import Data.List.Base public using (List ; []) renaming (_∷_ to infixr 20 _::_ ; _++_ to infixl 50 _++_ ; map to map-List)

infixl 55 _,,_
pattern _,,_ A Bs = _::_ Bs A

data _∈_ {ℓ : ULevel} {A : 𝒰 ℓ} : A -> List A -> 𝒰₀ where
  this : ∀{a as} -> a ∈ (a :: as)
  next : ∀{a b as} -> a ∈ as -> a ∈ (b :: as)


-------------------------------
-- Everything else (for now)

-- open import Data.Vec.Base public using (Vec ; _∷_ ; [] ; lookup) renaming (_++_ to append)
open import Data.Product public using ( _×_ ; _,_ ; Σ-syntax) renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Sum public renaming (_⊎_ to _+_) renaming (inj₁ to left ; inj₂ to right)
open import Data.Fin public using (Fin ; zero ; suc)
open import Data.Nat public using (ℕ ; zero ; suc)
open import Data.Unit public

open import Data.Empty public


--------------------------------------------------------------------------------
-- Custom notation
--------------------------------------------------------------------------------


∑_ : {A : 𝒰 ℓ} -> (B : A -> 𝒰 ℓ') -> 𝒰 (ℓ ⊔ ℓ')
∑_ {A = A} B = Σ-syntax A B

∏ : {A : 𝒰 ℓ} -> (B : A -> 𝒰 ℓ') -> 𝒰 (ℓ ⊔ ℓ')
∏ {A = A} B = (a : A) -> B a


cong : ∀{ℓ ℓ'} -> {A : Set ℓ} -> {B : Set ℓ'} {a b : A} -> (f : A -> B) -> a == b -> f a == f b
cong f refl = refl

infixl 20 _∙_
trans : ∀{ℓ} -> {A : Set ℓ} -> {a b c : A} -> a == b -> b == c -> a == c
trans refl p = p
_∙_ = trans

sym : ∀{ℓ} -> {A : Set ℓ} -> {a b : A} -> a == b -> b == a
sym refl = refl


subst : ∀{ℓ ℓ'} {A : Set ℓ} (P : A -> Set ℓ') -> {a b : A} -> (a == b) -> P a -> P b
subst P refl Pa = Pa

module _ {ℓ} {A : Set ℓ} where
  infix  3 _==-qed _∎
  infixr 2 _==⟨⟩_ _==⟨_⟩_

  _==⟨⟩_ : (x {y} : A) → x == y → x == y
  _ ==⟨⟩ x≡y = x≡y

  _==⟨_⟩_ : (x {y z} : A) → x == y → y == z → x == z
  _ ==⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _==-qed _∎ : (x : A) → x == x
  _ ==-qed  = refl
  _∎ = _==-qed

cong' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} → (f : A → B) → x == y → f x == f y
cong' = cong

syntax cong' f p = p |ctx| f
