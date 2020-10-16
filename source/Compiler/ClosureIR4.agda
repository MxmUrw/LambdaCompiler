
module Compiler.ClosureIR4 where

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

_::_ : ∀{A : 𝒰 ℓ} -> A -> List A -> List A
A :: (_ , Γ) = (_ , A ∷ Γ)


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

Ty2 = Ctx × BaseTy

CT : Ty -> Ctx × BaseTy
CT (ι A) = empty , A
CT (A ⇒ B) =
  let (As , R) = CT B
  in (As ,, A , R)

data _⊢2_ : Ctx -> Ty2 -> 𝒰₀ where
  app : ∀{Γ A Bs B} -> Γ ⊢2 ((A :: Bs) , B) -> Γ ⊢ A -> Γ ⊢2 (Bs , B)
  lam : ∀{Γ A Bs B} -> Γ ,, A ⊢2 (Bs , B) -> Γ ⊢2 ((A :: Bs) , B)
  -- var : ∀{Γ A} -> A ∈ Γ -> Γ ⊢2 (CT A)


data RetTy : 𝒰₀ where
  ι : BaseTy -> RetTy
  Closure : Ctx -> Ctx -> BaseTy -> RetTy

NT : (Ctx × BaseTy) -> Ty
NT (empty , A) = ι A
NT ((_ , A ∷ As) , B) = A ⇒ NT ((_ , As) , B)

data Value : Ctx -> Ty -> 𝒰₀
data Function : Ctx -> RetTy -> 𝒰₀ where
  makeClosure : ∀{Γ A} -> Function Γ (ι A) -> Function Γ (Closure Γ empty A)
  _&write_ : ∀{Γ Δ As A B} -> Function Γ (Closure Δ (A :: As) B) -> Value Γ ( A) -> Function Γ (Closure (Δ ,, A) As B)
  call : ∀{Δ A} -> Value Δ (NT (empty , A)) -> Function Δ (ι A)
  -- ret : ∀{Δ A} -> Value Δ A -> Function Δ A


data Value where
  var : ∀{Γ A} -> A ∈ Γ -> Value Γ A
  -- makeClosure : ∀{Δ Γ A} -> Function Γ (ι A) -> Value Δ (Closure Γ empty A)
  -- makeClosure : ∀{Γ Δ A} -> Function Γ (ι A) -> Value Δ (NT (Γ , A))

_++_ : ∀{A : 𝒰 ℓ} -> List A -> List A -> List A
_++_ (_ , v) (_ , w) = (_ , append v w)

-- writeFunT : Ctx -> Ty -> 𝒰₀
-- writeFunT Γ A = let (As , R) = CT A in Function Γ (Closure Γ As R)

writeBaseFun : ∀{Γ A} -> (t : Γ ⊢2 (empty , A)) -> Function Γ (ι A)
writeBaseFun = {!!}

writeBaseFun2 : ∀{Γ As A} -> (t : Γ ⊢2 (As , A)) -> Function (As ++ Γ) (ι A)
writeBaseFun2 = {!!}

_&writeCtx_ : ∀{Γ As B} -> Function Γ (Closure empty (As ++ Γ) B) -> Function Γ (Closure (Γ) As B)
_&writeCtx_ = {!!}

writeFun : ∀{Γ A As} -> (t : Γ ⊢2 (As , A)) -> Function Γ (Closure Γ As A)
writeFun {Γ} {A} {empty} t = (makeClosure (writeBaseFun2 t))
writeFun {Γ} {A} {_ , B ∷ Bs} (app t s) = {!!}
writeFun {Γ} {A} {_ , B ∷ Bs} (lam t) =
  let t2 = makeClosure (writeBaseFun2 t)
  in {!!}

