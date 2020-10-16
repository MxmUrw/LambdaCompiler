
module Compiler.ClosureIR6 where

open import Base.Prelude

-- List : 𝒰 ℓ -> 𝒰 ℓ
-- List A = ∑ Vec A

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

-- Ctx = List Ty

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

data List (A : 𝒰 ℓ) : 𝒰 ℓ where
  [] : List A
  _,,_ : List A -> A -> List A

pattern _::_ A Bs = _,,_ Bs A

_++_ : ∀{A : 𝒰 ℓ} -> List A -> List A -> List A
[] ++ w = w
(x :: v) ++ w = x :: (v ++ w)

_∈_ : ∀{A : 𝒰 ℓ} -> A -> List A -> 𝒰₀
_∈_ = {!!}


data RetTy : 𝒰₀
data Ty2 : 𝒰₀

Ctx2 = List Ty2
RCtx = List RetTy

data RTy2 : 𝒰₀

data RetTy where
  ι : BaseTy -> RetTy
  Closure : RCtx -> (RTy2) -> RetTy

data RTy2 where
  _⇉_ : RCtx -> BaseTy -> RTy2

data Ty2 where
  _⇉_ : Ctx2 -> BaseTy -> Ty2




-- CT : Ty -> Ctx × BaseTy
-- CT (ι A) = empty , A
-- CT (A ⇒ B) =
--   let (As , R) = CT B
--   in (As ,, A , R)

data _⊢2_ : Ctx2 -> Ty2 -> 𝒰₀ where
  app : ∀{Γ A Bs B} -> Γ ⊢2 ((A :: Bs) ⇉ B) -> Γ ⊢2 A -> Γ ⊢2 (Bs ⇉ B)
  lam : ∀{Γ A Bs B} -> Γ ,, A ⊢2 (Bs ⇉ B) -> Γ ⊢2 ((A :: Bs) ⇉ B)
  var : ∀{Γ A} -> A ∈ Γ -> Γ ⊢2 A


data Value : RCtx -> RetTy -> 𝒰₀
data ValueSeq : RCtx -> RCtx -> 𝒰₀
data Function : RCtx -> RetTy -> 𝒰₀
data ValueSeq where
  init : ∀{Γ} -> ValueSeq Γ Γ
  _&_ : ∀{Γ Δ A} -> ValueSeq Γ Δ -> Value Δ A -> ValueSeq Γ (Δ ,, A)

infixl 20 _&_

data Value where
  call : ∀{Γ Δ A} -> Value Γ (Closure Δ ([] ⇉ A)) -> Value Γ (ι A)
  makeClosure : ∀{Γ Δ A} -> Function Γ (ι A) -> Value Δ (Closure [] (Γ ⇉ A))
  weak : ∀{Δ Γ A} -> Value Γ A -> Value (Γ ++ Δ) A
  write : ∀{Γ Δ A As B} -> Value Γ A -> Value Γ (Closure Δ ((As ,, A) ⇉ B)) -> Value Γ (Closure (Δ ,, A) (As ⇉ B))
  proj : ∀{Γ A} -> A ∈ Γ -> Value Γ A


data Function where
  ret : ∀{Γ Δ A} -> ValueSeq Γ (Δ ,, A) -> Function Γ A


lmr : Ctx2 -> RCtx

mr : Ty2 -> RetTy
mr (A ⇉ B) = Closure [] (lmr A ⇉ B)

lmr [] = []
lmr (A :: As) = mr A :: lmr As

writeVal : ∀{Γ A} -> (t : Γ ⊢2 (A)) -> Value (lmr Γ) (mr A)
writeVal = {!!}

writeBaseFun2 : ∀{Γ As A} -> (t : Γ ⊢2 (As ⇉ A)) -> Function (lmr Γ ++ lmr As) (ι A)
writeBaseFun2 {Γ} {As} (app {A = (Xs ⇉ X)} t s) =
  let t2 = writeVal t
      s2 = writeVal s
      a = write (s2) (t2)
      -- p = init {lmr Γ ++ lmr As}
      --     & write (weak s2) (weak t2)
      --     & {!!}
  in {!!} -- ret p
writeBaseFun2 (lam t) = {!!}
writeBaseFun2 (var x) = {!!}
  -- let -- t2 = writeBaseFun2 t
  --     t4 = writeVal t
  --     s2 = writeVal s
  -- --     a = t4 &write s2
  -- --     a2 = moveCtx a
  -- -- in a2 &retVal
  -- in {!!}






  -- proj : ∀{Γ A} -> ([] , A) ∈ Γ -> Value Γ ([] , A)

{-
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

-}
