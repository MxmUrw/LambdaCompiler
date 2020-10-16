
module Compiler.ClosureIR7 where

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

data _∈_ {A : 𝒰 ℓ} : A -> List A -> 𝒰₀ where
  this : ∀{a as} -> a ∈ (a :: as)
  next : ∀{a b as} -> a ∈ as -> a ∈ (b :: as)

-- _∈_ = {!!}


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
  call : ∀{Γ Δ A} -> (Closure Δ ([] ⇉ A)) ∈ Γ -> Value Γ (ι A)
  makeClosure : ∀{Γ Δ A} -> Function Γ (ι A) -> Value Δ (Closure [] (Γ ⇉ A))
  weak : ∀{Δ Γ A} -> Value Γ A -> Value (Γ ++ Δ) A
  weak1 : ∀{B Γ A} -> Value (Γ) A -> Value (Γ ,, B) A
  inline : ∀{Γ A} -> Function Γ A -> Value Γ A
  write : ∀{Γ Δ A As B} -> A ∈ Γ -> (Closure Δ ((As ,, A) ⇉ B)) ∈ Γ -> Value Γ (Closure (Δ ,, A) (As ⇉ B))
  -- proj : ∀{Γ A} -> A ∈ Γ -> Value Γ A


data Function where
  ret : ∀{Γ Δ A} -> ValueSeq Γ (Δ ,, A) -> Function Γ A

infixr 20 _::_

lmr : Ctx2 -> RCtx
lmr-with : Ctx2 -> Ctx2 -> RCtx

mr : Ty2 -> RetTy
mr (A ⇉ B) = Closure [] (lmr A ⇉ B)

mr-with : Ctx2 -> Ty2 -> RetTy
mr-with Γ (A ⇉ B) = Closure (lmr Γ) (lmr-with Γ A ⇉ B)

lmr-with Γ [] = []
lmr-with Γ (A :: As) = mr-with Γ A :: lmr-with Γ As

lmr [] = []
lmr (A :: As) = mr A :: lmr As

writeCtx : ∀{Γ₀ Γ Δ Ξ A} -> Closure Δ (Ξ ⇉ A) ∈ Γ₀ -> Value (Γ₀ ++ (Γ ++ Ξ)) (Closure (Δ ++ Ξ) ([] ⇉ A))
writeCtx = {!!}
-- writeCtx : ∀{Γ₀ Γ Δ B} -> Value Γ (Γ₀ ++ (Γ ++ Δ), B) -> Value Γ (Γ₀ ++ Δ , B)

compileVal : ∀{Γ A} -> (t : Γ ⊢2 (A)) -> Value (lmr Γ) (mr A) -- (Closure (lmr Γ) (lmr As ⇉ A))

compileValK : ∀{Γ A} -> (t : Γ ⊢2 (A)) -> Value (lmr Γ) (mr-with Γ A) -- (Closure (lmr Γ) (lmr As ⇉ A))
compileValK = {!!}

compileValBase : ∀{Γ A} -> (t : Γ ⊢2 ([] ⇉ A)) -> Value (lmr Γ) (Closure [] ([] ⇉ A))
compileValBaseK : ∀{Γ A} -> (t : Γ ⊢2 ([] ⇉ A)) -> Value (lmr Γ) (Closure (lmr Γ) ([] ⇉ A))

compileValBaseK {Γ} {A} (app t s) =
  let p = init {Γ = lmr Γ}
          & compileVal t
          & weak1 (compileVal s)
          & write this (next this)
      z = ret p
  in inline (ret {!!})
compileValBaseK {Γ} {A} (var x) = {!!}

compileValBase {Γ} {A} (app t s) =
  let p = init {Γ = lmr Γ}
          & compileVal t
          & weak1 (compileVal s)
          & write this (next this)
          & call this
          & {!!}

      q = ret p
      z = makeClosure q
      -- z = inline q
      -- z = init
      --     & inline q
      --     & makeClosure this
  in {!!} -- inline q & makeClosure
compileValBase (var x) = {!!}

compileVal {Γ} {[] ⇉ A} t = {!!}
compileVal {Γ} {(x :: As) ⇉ A} t = {!!}
-- compileVal (app t s) = {!!}
-- compileVal (lam t) = {!!}
-- compileVal (var x) = {!!}

compileBaseFunK : ∀{Γ As A} -> (t : Γ ⊢2 (As ⇉ A)) -> Function (lmr Γ ++ lmr-with Γ As) (ι A)
compileBaseFunK {Γ} {As} (app {A = (Xs ⇉ X)} t s) =
  let p = init {lmr Γ ++ lmr-with Γ As}
          & weak (compileValK t)
          & weak1 (weak (compileValK s))
          & write (this) (next this)
          & writeCtx {Γ₀ = _ :: _ :: _ :: []} {Γ = lmr Γ} {Ξ = lmr-with Γ As} this -- {Γ = lmr Γ} {Ξ = lmr As} this
          & call this
  in ret p
compileBaseFunK (lam t) = {!!}
compileBaseFunK (var x) = {!!}

compileBaseFun : ∀{Γ As A} -> (t : Γ ⊢2 (As ⇉ A)) -> Function (lmr Γ ++ lmr As) (ι A)
compileBaseFun {Γ} {As} (app {A = (Xs ⇉ X)} t s) =
  let p = init {lmr Γ ++ lmr As}
          & weak (compileVal t)
          & weak1 (weak (compileVal s))
          & write (this) (next this)
          & writeCtx {Γ₀ = _ :: _ :: _ :: []} {Γ = lmr Γ} {Ξ = lmr As} this
          & call this
  in ret p
compileBaseFun (lam t) = {!!}
compileBaseFun (var x) = {!!}
  -- let -- t2 = compileBaseFun t
  --     t4 = compileVal t
  --     s2 = compileVal s
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

compileVal : ∀{Γ A As} -> (t : Γ ⊢2 (As , A)) -> Value Γ (As , A)

writeCtx : ∀{Γ₀ Γ Δ B} -> Value Γ (Γ₀ ++ (Γ ++ Δ), B) -> Value Γ (Γ₀ ++ Δ , B)
moveCtx : ∀{Γ Δ As A} -> Value Γ ((As ++ Δ) , A) -> Value (Γ ++ Δ) (As , A)
moveCtx = {!!}

writeFun : ∀{Γ A As} -> (t : Γ ⊢2 (As , A)) -> Function Γ (Closure Γ (As , A))

compileBaseFun : ∀{Γ As A} -> (t : Γ ⊢2 (As , A)) -> Function (Γ ++ As) (ι A)
compileBaseFun (app {A = (Xs , X)} t s) =
  let -- t2 = compileBaseFun t
      t4 = compileVal t
      s2 = compileVal s
  --     a = t4 &write s2
  --     a2 = moveCtx a
  -- in a2 &retVal
  in {!!}

compileBaseFun (lam t) =
  let t2 = compileBaseFun t
  in {!!}
compileBaseFun {Γ} {As} (var x) = moveCtx {Γ = Γ} (proj x) &retVal

writeCtx {[]} {D} {B} v = {!!}
writeCtx {x :: G} {D} {B} v = {!!}
  -- let v1 = (v &write {!!})
  -- in {!!}




compileValBase : ∀{Γ A} -> Γ ⊢2 ([] , A) -> Value Γ ([] , A)
compileValBase (app t s) = {!!}
  -- let x = (compileVal t) &write (compileVal s)
  -- in x
compileValBase (var x) = {!!}

compileVal {Γ} {A} {[]} t = compileValBase t -- &retClosure
compileVal {Γ} {A} {x :: As} (app t s) = {!!} -- (compileVal t) &write (compileVal s)
compileVal {Γ} {A} {x :: As} (lam t) =
  let t2 = makeClosure {Δ = Γ} (compileBaseFun t)
      t3 = writeCtx {Γ₀ = ([] ,, x)} {Γ = Γ} t2
  in t3 -- &retClosure
compileVal {Γ} {A} {x :: As} (var x₁) = {!!}


writeFun t = compileVal t &retClosure
-- writeFun {Γ} {A} {[]} t = compileValBase t &retClosure
-- writeFun {Γ} {A} {x :: As} (app t s) = {!!}
-- writeFun {Γ} {A} {x :: As} (lam t) =
--   let t2 = makeClosure {Δ = Γ} (compileBaseFun t)
--       t3 = writeCtx {Γ₀ = ([] ,, x)} {Γ = Γ} t2
--   in t3 &retClosure
-- writeFun {Γ} {A} {x :: As} (var x₁) = {!!}
-- writeFun : ∀{Γ A As} -> (t : Γ ⊢2 (As , A)) -> Function Γ (Closure Γ As A)
-- writeFun {Γ} {A} {empty} t = (makeClosure (compileBaseFun t))
-- writeFun {Γ} {A} {_ , B ∷ Bs} (app t s) = {!!}
-- writeFun {Γ} {A} {_ , B ∷ Bs} (lam t) =
--   let t2 = makeClosure (compileBaseFun t)
--   in {!!}

-}
