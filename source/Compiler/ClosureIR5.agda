
module Compiler.ClosureIR5 where

open import Base.Prelude

List : 𝒰 ℓ -> 𝒰 ℓ
List A = ∑ Vec A

data BaseTy : 𝒰₀ where
  BB : BaseTy

data Ty : 𝒰₀ where
  ι : BaseTy -> Ty
  _⇒_ : Ty -> Ty -> Ty

-- _,,_ : ∀{A : 𝒰 ℓ} -> List A -> A -> List A
-- (_ , Γ) ,, A = (_ , A ∷ Γ)

-- _::_ : ∀{A : 𝒰 ℓ} -> A -> List A -> List A
-- A :: (_ , Γ) = (_ , A ∷ Γ)


infixl 55 _,,_
-- syntax n , Γ ,, A = suc n , A ∷ Γ
-- pattern (A ∷ (n , Γ)) = 

Ctx = List Ty

infixr 70 _⇒_
infixr 50 _⊢2_

-- _∈_ : ∀{A : 𝒰 ℓ} (e : A) (v : List A) -> 𝒰 ℓ -- -> (i : Fin (fst v)) -> A
-- _∈_ e (_ , v) = ∑ λ i -> lookup v i == e

-- syntax Elem V i = i ∈ V

pattern empty = (_ , [])

-- data _⊢_ : Ctx -> Ty -> 𝒰₀ where
--   app : ∀{Γ A B} -> Γ ⊢ A ⇒ B -> Γ ⊢ A -> Γ ⊢ B
--   lam : ∀{Γ A B} -> Γ ,, A ⊢ B -> Γ ⊢ A ⇒ B
--   var : ∀{Γ A} -> A ∈ Γ -> Γ ⊢ A


data Ctx2 : 𝒰₀
Ty2 = Ctx2 × BaseTy

data Ctx2 where
  [] : Ctx2
  _,,_ : Ctx2 -> Ty2 -> Ctx2

pattern _::_ A Bs = _,,_ Bs A

_∈_ : Ty2 -> Ctx2 -> 𝒰₀
_∈_ = {!!}

-- CT : Ty -> Ctx × BaseTy
-- CT (ι A) = empty , A
-- CT (A ⇒ B) =
--   let (As , R) = CT B
--   in (As ,, A , R)

data _⊢2_ : Ctx2 -> Ty2 -> 𝒰₀ where
  app : ∀{Γ A Bs B} -> Γ ⊢2 ((A :: Bs) , B) -> Γ ⊢2 A -> Γ ⊢2 (Bs , B)
  lam : ∀{Γ A Bs B} -> Γ ,, A ⊢2 (Bs , B) -> Γ ⊢2 ((A :: Bs) , B)
  var : ∀{Γ A} -> A ∈ Γ -> Γ ⊢2 A


data RetTy : 𝒰₀ where
  ι : BaseTy -> RetTy
  Closure : Ctx2 -> (Ty2) -> RetTy

-- NT : (Ctx × BaseTy) -> Ty
-- NT (empty , A) = ι A
-- NT ((_ , A ∷ As) , B) = A ⇒ NT ((_ , As) , B)

_++_ : Ctx2 -> Ctx2 -> Ctx2
[] ++ w = w
(x :: v) ++ w = x :: (v ++ w)

data Value : Ctx2 -> Ty2 -> 𝒰₀
data Function : Ctx2 -> RetTy -> 𝒰₀ where
  _&retVal : ∀{Δ A} -> Value Δ ([] , A) -> Function Δ (ι A)
  _&retClosure : ∀{Δ A} -> Value Δ A -> Function Δ (Closure Δ A)
--   makeClosure : ∀{Γ A} -> Function Γ (ι A) -> Function Γ (Closure Γ empty A)
--   _&write_ : ∀{Γ Δ As A B} -> Function Γ (Closure Δ (A :: As) B) -> Value Γ ( A) -> Function Γ (Closure (Δ ,, A) As B)
--   call : ∀{Δ A} -> Value Δ (NT (empty , A)) -> Function Δ (ι A)
--   -- ret : ∀{Δ A} -> Value Δ A -> Function Δ A

-- iValue : Ctx2 -> Ty2 -> 𝒰₀
-- iValue Γ ([] , B) = Value Γ ([] , B)
-- iValue Γ ((A :: As) , B) = 

data Value where
  makeClosure : ∀{Γ Δ A} -> Function Γ (ι A) -> Value Δ (Γ , A)
  _&write_ : ∀{Γ Δ A B} -> Value Γ ((Δ ,, (A)), B) -> Value Γ (A) -> Value Γ (Δ , B)
  weak : ∀{Γ Δ A} -> Value Γ A -> Value (Γ ++ Δ) A
  -- proj : ∀{Γ A} -> ([] , A) ∈ Γ -> Value Γ ([] , A)
  proj : ∀{Γ A} -> A ∈ Γ -> Value Γ A

Interp : BaseTy -> 𝒰₀
Interp BB = ℕ

Env : Ctx2 -> 𝒰₀
EnvT : Ty2 -> 𝒰₀

EnvT (A , B) = Env A -> Interp B

Env ([]) = ⊤
Env (A :: As) = EnvT A × Env As


-- eval2 : ∀{As A} -> Value [] (As , A) -> Env As -> Interp A
-- eval2 v = {!!}


eval : ∀{Γ As A} -> Value Γ (As , A) -> (Env Γ -> Env As -> Interp A)
eval (makeClosure x) e as = {!!}
eval (v &write w) e as =
  let rw = eval w e
      rv = eval v e
  in rv (rw , as)
eval (weak v) = {!!}
eval (proj x) = {!!}

  -- call : ∀{Γ A As B} -> Value Γ A -> Value Γ ((A :: As), B) -> Value Γ (As , B)
  -- call : ∀{Γ A} -> Value Γ 
  -- weak : ∀{Γ A B} -> Value (Γ ,, A)

--   var : ∀{Γ A} -> A ∈ Γ -> Value Γ A
--   -- makeClosure : ∀{Δ Γ A} -> Function Γ (ι A) -> Value Δ (Closure Γ empty A)
--   -- makeClosure : ∀{Γ Δ A} -> Function Γ (ι A) -> Value Δ (NT (Γ , A))

-- _++_ (_ , v) (_ , w) = (_ , append v w)

-- -- writeFunT : Ctx -> Ty -> 𝒰₀
-- -- writeFunT Γ A = let (As , R) = CT A in Function Γ (Closure Γ As R)

-- writeBaseFun : ∀{Γ A} -> (t : Γ ⊢2 ([] , A)) -> Function Γ (ι A)
-- writeBaseFun = {!!}

writeVal : ∀{Γ A As} -> (t : Γ ⊢2 (As , A)) -> Value Γ (As , A)

writeCtx : ∀{Γ₀ Γ Δ B} -> Value Γ (Γ₀ ++ (Γ ++ Δ), B) -> Value Γ (Γ₀ ++ Δ , B)
moveCtx : ∀{Γ Δ As A} -> Value Γ ((As ++ Δ) , A) -> Value (Γ ++ Δ) (As , A)
moveCtx = {!!}

writeFun : ∀{Γ A As} -> (t : Γ ⊢2 (As , A)) -> Function Γ (Closure Γ (As , A))

writeBaseFun2 : ∀{Γ As A} -> (t : Γ ⊢2 (As , A)) -> Function (Γ ++ As) (ι A)
writeBaseFun2 (app {A = (Xs , X)} t s) =
  let -- t2 = writeBaseFun2 t
      t4 = writeVal t
      s2 = writeVal s
  --     a = t4 &write s2
  --     a2 = moveCtx a
  -- in a2 &retVal
  in {!!}

writeBaseFun2 (lam t) =
  let t2 = writeBaseFun2 t
  in {!!}
writeBaseFun2 {Γ} {As} (var x) = moveCtx {Γ = Γ} (proj x) &retVal

writeCtx {[]} {D} {B} v = {!!}
writeCtx {x :: G} {D} {B} v = {!!}
  -- let v1 = (v &write {!!})
  -- in {!!}




writeValBase : ∀{Γ A} -> Γ ⊢2 ([] , A) -> Value Γ ([] , A)
writeValBase (app t s) = {!!}
  -- let x = (writeVal t) &write (writeVal s)
  -- in x
writeValBase (var x) = {!!}

writeVal {Γ} {A} {[]} t = writeValBase t -- &retClosure
writeVal {Γ} {A} {x :: As} (app t s) = {!!} -- (writeVal t) &write (writeVal s)
writeVal {Γ} {A} {x :: As} (lam t) =
  let t2 = makeClosure {Δ = Γ} (writeBaseFun2 t)
      t3 = writeCtx {Γ₀ = ([] ,, x)} {Γ = Γ} t2
  in t3 -- &retClosure
writeVal {Γ} {A} {x :: As} (var x₁) = {!!}


writeFun t = writeVal t &retClosure
-- writeFun {Γ} {A} {[]} t = writeValBase t &retClosure
-- writeFun {Γ} {A} {x :: As} (app t s) = {!!}
-- writeFun {Γ} {A} {x :: As} (lam t) =
--   let t2 = makeClosure {Δ = Γ} (writeBaseFun2 t)
--       t3 = writeCtx {Γ₀ = ([] ,, x)} {Γ = Γ} t2
--   in t3 &retClosure
-- writeFun {Γ} {A} {x :: As} (var x₁) = {!!}
-- writeFun : ∀{Γ A As} -> (t : Γ ⊢2 (As , A)) -> Function Γ (Closure Γ As A)
-- writeFun {Γ} {A} {empty} t = (makeClosure (writeBaseFun2 t))
-- writeFun {Γ} {A} {_ , B ∷ Bs} (app t s) = {!!}
-- writeFun {Γ} {A} {_ , B ∷ Bs} (lam t) =
--   let t2 = makeClosure (writeBaseFun2 t)
--   in {!!}
