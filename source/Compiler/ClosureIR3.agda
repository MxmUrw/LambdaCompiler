
module Compiler.ClosureIR3 where

open import Base.Prelude

List : 𝒰 ℓ -> 𝒰 ℓ
List A = ∑ Vec A

data BaseTy : 𝒰₀ where
  BB : BaseTy

data Ty : 𝒰₀ where
  ι : BaseTy -> Ty
  _⇒_ : Ty -> Ty -> Ty

_,,_ : ∀{A : 𝒰 ℓ} -> List A -> A -> List A
(_ , Γ) ,, A = (_ , A ∷ Γ)

infixl 55 _,,_
-- syntax n , Γ ,, A = suc n , A ∷ Γ
-- pattern (A ∷ (n , Γ)) = 

Ctx = List Ty

infixr 70 _⇒_
infixr 50 _⊢_

_∈_ : ∀{A : 𝒰 ℓ} (e : A) (v : List A) -> 𝒰 ℓ -- -> (i : Fin (fst v)) -> A
_∈_ e (_ , v) = ∑ λ i -> lookup v i == e

-- syntax Elem V i = i ∈ V

pattern empty = (_ , [])

data _⊢_ : Ctx -> Ty -> 𝒰₀ where
  app : ∀{Γ A B} -> Γ ⊢ A ⇒ B -> Γ ⊢ A -> Γ ⊢ B
  lam : ∀{Γ A B} -> Γ ,, A ⊢ B -> Γ ⊢ A ⇒ B
  var : ∀{Γ A} -> A ∈ Γ -> Γ ⊢ A

data RetTy : 𝒰₀ where
  ι : BaseTy -> RetTy
  Closure : Ctx -> Ctx -> BaseTy -> RetTy

data Function : Ctx -> RetTy -> 𝒰₀ where
  makeClosure : ∀{Γ A} -> Function Γ (ι A) -> Function Γ (Closure Γ empty A)

CT : Ty -> Ctx × BaseTy
CT (ι A) = empty , A
CT (A ⇒ B) =
  let (As , R) = CT B
  in (As ,, A , R)

writeFunT : Ctx -> Ty -> 𝒰₀
writeFunT Γ A = let (As , R) = CT A in Function Γ (Closure Γ As R)

writeBaseFun : ∀{Γ A} -> (t : Γ ⊢ ι A) -> Function Γ (ι A)
writeBaseFun = {!!}

writeFun : ∀{Γ A} -> (t : Γ ⊢ A) -> writeFunT Γ A
writeFun {Γ} {ι x} t = makeClosure (writeBaseFun t)
writeFun {Γ} {A ⇒ B} t = {!!}


-- writeFunT : Ctx -> Ty -> 𝒰₀
-- writeFunT Γ (ι A) = Function Γ (ι A)
-- writeFunT Γ (A ⇒ B) = Function Γ (Closure Γ (_ , A ∷ []) B)


-- writeFunT : Ctx -> Ty -> 𝒰₀
-- writeFunT Γ (ι A) = Function Γ (ι A)
-- writeFunT Γ (A ⇒ B) = Function Γ (Closure Γ (_ , A ∷ []) B)

-- writeFun : ∀{Γ A} -> (t : Γ ⊢ A) -> writeFunT Γ A 

-- writeBaseFun : ∀{Γ A} -> (t : Γ ⊢ ι A) -> Function Γ (ι A)
-- writeBaseFun (app t t₁) = {!!}
-- writeBaseFun (var x) = {!!}

-- writeArrFun : ∀{Γ A B} -> (t : Γ ⊢ A ⇒ B) -> Function Γ (Closure Γ (_ , A ∷ []) B)
-- writeArrFun (app t s) =
--   let t2 = writeArrFun t
--       s2 = writeFun s
--   in {!!}
-- writeArrFun (lam t) = {!!}
-- writeArrFun (var x) = {!!}

-- writeFun {A = ι x} t = writeBaseFun t
-- writeFun {A = A ⇒ A₁} t = writeArrFun t



