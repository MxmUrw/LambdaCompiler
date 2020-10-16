
module Compiler.ClosureIR2 where

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

-- FunTy : (Γ : Ctx) -> (A : Ty) -> 𝒰₀
-- FunTy 

CloTy : 𝒰₀
CloTy = List Ty × BaseTy

toCloTy : Ty -> CloTy
toCloTy (ι x) = empty , x
toCloTy (A ⇒ B) = let (Bs , B) = toCloTy B in (Bs ,, A , B)

data Value : Ctx -> Ty -> 𝒰₀
data Function : Ctx -> CloTy -> 𝒰₀ where

data Value where

compileFun : ∀{Γ A} -> (t : Γ ⊢ A) -> Function Γ (toCloTy A)
compileFun t = {!!}

  -- call : ∀{Γ A B} -> Value Γ (A ⇒ B) -> Value Γ A -> Function Γ B
  -- call : ∀{Γ A B} -> Value Γ A -> 
  -- defer : ∀{Γ A B} -> Value (Γ ,, A) B -> Function Γ (A ⇒ B)
  -- call : ∀{Γ A B} -> Value (Γ ,, ι A) (ι B) -> Function Γ A -> Function (Γ) B


  -- proj : ∀{Γ A} -> A ∈ Γ -> Function Γ A
  -- set₀ : ∀{Γ A B} -> Value Γ (A ⇒ B) -> Value Γ A -> Function Γ B
  -- val : ∀{Γ A} -> Function Γ A -> Value Γ (A)
  -- -- defer : ∀{Γ A B} -> Value (Γ ,, A) B -> Function Γ (A ⇒ B)
  -- defer : ∀{Γ A B} -> Value (Γ ,, A) B -> Value Γ (A ⇒ B)
  -- proj : ∀{Γ A} -> A ∈ Γ -> Value Γ A
  -- app : ∀{Γ A B} -> Value (Γ ,, ι A) B -> Function Γ A -> Value Γ B

-- compileT : ∀{Γ A} -> (t : Γ ⊢ A) -> 𝒰₀
-- compileT = ?

-- FunctionH : Ctx -> Ty -> 𝒰₀
-- FunctionH Γ (ι x) = Function Γ (ι x)
-- FunctionH Γ (A ⇒ B) = FunctionH (Γ ,, A) B

-- set₀H : ∀{Γ A B} -> Value Γ (A ⇒ B) -> Value Γ A -> FunctionH Γ B
-- set₀H {Γ} {A} {ι x} t s = {!!}
-- set₀H {Γ} {A} {B ⇒ B₁} t s = {!!}

-- compileVal : ∀{Γ A} -> (t : Γ ⊢ A) -> Value Γ A
-- compileValLam : ∀{Γ A B} -> (t : Γ ,, A ⊢ B) -> Value Γ (A ⇒ B)
-- compileValApp : ∀{Γ A B} -> (t : Γ ⊢ A ⇒ B) (s : Γ ⊢ A) -> Value Γ B

-- compileFun : ∀{Γ A} -> (t : Γ ⊢ ι A) -> Function Γ (ι A)
-- -- compileFun {Γ} {ι x} (app t s) = set₀ (compileVal t) (compileVal s)
-- -- compileFun {Γ} {A ⇒ A₁} (app t s) = {!!}
-- compileFun {Γ} {A} (app t s) = set₀ (compileVal t) (compileVal s)
-- -- compileFun {Γ} {A ⇒ B} (lam t) = defer (val (set₀ ({!!}) {!!}))  -- (val (compileFun t)) ?
-- -- set₀ (defer (val {!!})) {!!}  -- (val (compileFun t)) ?
-- compileFun (var x) = proj x

-- compileVal (app t s) = compileValApp t s -- val (compileFun (app t t₁))
-- compileVal (lam t) = compileValLam t
--   -- let f = compileVal t
--   -- in ({!!})
-- compileVal (var x) = {!!}

-- compileValLam {Γ} {A} {ι x} t = let t1 = compileFun t in (defer (val t1))
-- compileValLam {Γ} {A} {B ⇒ B₁} (app t t₁) = defer (compileVal (app t t₁))
-- compileValLam {Γ} {A} {B ⇒ B₁} (lam t) = defer (compileValLam t)
-- compileValLam {Γ} {A} {B ⇒ B₁} (var x) = defer (compileVal (var x))

-- compileValApp {Γ} {A} {ι x} t s = val (compileFun (app t s))
-- compileValApp {Γ} {A} {B ⇒ B₁} t = {!!}
