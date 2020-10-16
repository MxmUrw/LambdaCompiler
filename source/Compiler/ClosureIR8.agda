

module Compiler.ClosureIR8 where

open import Base.Prelude

-- List : 𝒰 ℓ -> 𝒰 ℓ
-- List A = ∑ Vec A

data BaseTy : 𝒰₀ where
  NN : BaseTy

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
  Closure : (RTy2) -> RetTy

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
  call : ∀{Γ A} -> (Closure ([] ⇉ A)) ∈ Γ -> Value Γ (ι A)
  makeClosure : ∀{Γ Δ A} -> Function Γ (ι A) -> Value Δ (Closure (Γ ⇉ A))
  weak : ∀{Δ Γ A} -> Value Γ A -> Value (Γ ++ Δ) A
  weak1 : ∀{B Γ A} -> Value (Γ) A -> Value (Γ ,, B) A
  inline : ∀{Γ A} -> Function Γ A -> Value Γ A
  write2 : ∀{Γ As A As2 B} -> A ∈ Γ -> (Closure ((As ++ (([] ,, A) ++ As2)) ⇉ B)) ∈ Γ -> Value Γ (Closure (As ++ As2 ⇉ B))
  proj : ∀{Γ A} -> A ∈ Γ -> Value Γ A

List-++-[] :  ∀{A : 𝒰 ℓ} -> (v : List A) -> v ++ ([]) == v
List-++-[] [] = refl
List-++-[] (x :: v) = cong (x ::_) (List-++-[] v)



write : ∀{Γ A As B} -> A ∈ Γ -> (Closure ((As ,, A) ⇉ B)) ∈ Γ -> Value Γ (Closure (As ⇉ B))
write {Γ} {A} {As} {B} i c = write2 {As = []} {A = A} {As2 = As} {B = B} i c

data Function where
  ret : ∀{Γ Δ A} -> ValueSeq Γ (Δ ,, A) -> Function Γ A

-------------------------------------------------
-- Interpret

EnvT : RCtx -> 𝒰₀

BTyT : BaseTy -> 𝒰₀
BTyT (NN) = ℕ

TyT : RetTy -> 𝒰₀
TyT (ι a) = BTyT a
TyT (Closure (x ⇉ y)) = EnvT x -> BTyT y

EnvT [] = ⊤
EnvT (x :: G) = TyT x × EnvT G

-- evalClosure : ∀{A} -> Closure ([] ⇉ A) 

getCtx : ∀{Γ A} -> A ∈ Γ -> EnvT Γ -> TyT A
getCtx this (x , _) = x
getCtx (next i) (_ , e) = getCtx i e

eval : ∀{Γ A} -> Value Γ A -> EnvT Γ -> TyT A
evalSeq : ∀{Γ Δ} -> ValueSeq Γ Δ -> EnvT Γ -> EnvT Δ
evalSeq init x = x
evalSeq (s & x) e = let sv = evalSeq s e
                        xv = eval x sv
                    in xv , sv

evalFun : ∀{Γ A} -> Function Γ A -> EnvT Γ -> TyT A
evalFun (ret x) e = let (r , _) = evalSeq x e
                    in r

evalWeak : ∀{Γ Δ} -> EnvT (Γ ++ Δ) -> EnvT Γ
evalWeak {[]} {D} e = tt
evalWeak {x :: G} {D} (v1 , vr) = v1 , evalWeak vr

splice : ∀{Γ A Δ} -> EnvT (Γ ++ Δ) -> TyT A -> EnvT (Γ ++ (A :: Δ))
splice {[]} {A} {D} e a = a , e
splice {G0 :: G} {A} {D} (x , e) a = x , splice e a

eval (call x) e = getCtx x e tt
eval (makeClosure f) _ e2 = evalFun f e2
eval (weak {Δ = D} {Γ = G} v) e = eval v (evalWeak e)
eval (weak1 v) (_ , e) = eval v e
eval (inline x) e = evalFun x e
eval (write2 t s) e e2 =
  let vt = getCtx t e
      vs = getCtx s e
  in vs (splice e2 vt)
eval (proj x) e = getCtx x e

-------------------------------------------------

infixr 20 _::_

lmr : Ctx2 -> RCtx
-- lmr-with : Ctx2 -> Ctx2 -> RCtx

mr : Ty2 -> RetTy
mr (A ⇉ B) = Closure (lmr A ⇉ B)

-- mr-with : Ctx2 -> Ty2 -> RetTy
-- mr-with Γ (A ⇉ B) = Closure (lmr Γ) (lmr-with Γ A ⇉ B)

-- lmr-with Γ [] = []
-- lmr-with Γ (A :: As) = mr-with Γ A :: lmr-with Γ As

lmr [] = []
lmr (A :: As) = mr A :: lmr As

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



infixl 50 _++_

writeCtx2 : ∀{Γ₀ Γ Γ₁ Δ A} -> Closure (Γ₀ ++ (Γ ++ Γ₁) ⇉ A) ∈ Δ -> Γ ⊆ Δ -> Value Δ (Closure ((Γ₀ ++ Γ₁) ⇉ A))
writeCtx2 {G0} {[]} {G1} {D} c g = proj c
writeCtx2 {G0} {x :: G} {G1} {D} {A} c g =
  let qq = write2 {Γ = D} {As = G0} {A = x} {As2 = (G ++ G1)} {B = A} (trans-∈-⊆ this g) c
      p = init {Γ = D}
          & qq
          & writeCtx2 {Γ₀ = G0} {Γ = G} {Γ₁ = G1} this (trans-⊆ (skip refl) (trans-⊆ g (skip refl)))
  in inline (ret p)

writeCtx : ∀{Γ₀ Γ Ξ A} -> Closure (Ξ ⇉ A) ∈ Γ₀ -> Value (Γ₀ ++ (Γ ++ Ξ)) (Closure ([] ⇉ A))
writeCtx {Γ₀} {Γ} {Ξ} {A} c with writeCtx2 {Γ₀ = []} {Γ = Ξ} {Γ₁ = []} {Δ = Γ₀ ++ (Γ ++ Ξ)}
... | ff rewrite List-++-[] Ξ = ff (trans-∈-⊆ c (++→⊆-r _)) (trans-⊆ (++→⊆-l Γ) (++→⊆-l Γ₀))

compileVal : ∀{Γ A} -> (t : Γ ⊢2 (A)) -> Value (lmr Γ) (mr A) -- (Closure (lmr Γ) (lmr As ⇉ A))
compileBaseFun : ∀{Γ As A} -> (t : Γ ⊢2 (As ⇉ A)) -> Function (lmr Γ ++ lmr As) (ι A)


mr-∈ : ∀{A Γ} -> A ∈ Γ -> mr A ∈ lmr Γ
mr-∈ {x ⇉ x₁} {.(x ⇉ x₁) :: G} this = this
mr-∈ {x ⇉ x₁} {x₂ :: G} (next i) = next (mr-∈ i)

compileVal {Γ} {(_ ⇉ _)} (app t s) =
  let p = init {Γ = lmr Γ}
          & compileVal t
          & weak1 (compileVal s)
          & write this (next this)
  in inline (ret p)
compileVal {Γ} {.((_ :: _) ⇉ _)} (lam t) =
  let p = init {Γ = lmr (Γ)}
           & makeClosure (compileBaseFun t)
           & writeCtx2 {Γ₀ = [] ,, _} this (skip refl)

  in inline (ret p)
compileVal {Γ} {A} (var x) = proj (mr-∈ x)



compileBaseFun {Γ} {As} (app {A = (Xs ⇉ X)} t s) =
  let p = init {lmr Γ ++ lmr As}
          & weak (compileVal t)
          & weak1 (weak (compileVal s))
          & write (this) (next this)
          & writeCtx {Γ₀ = _ :: _ :: _ :: []} {Γ = lmr Γ} {Ξ = lmr As} this
          & call this
  in ret p
compileBaseFun {Γ} {As ,, A} (lam {B = B} t) =
  let t2 = compileBaseFun t
      p = init {lmr Γ ++ (mr A :: lmr As)}
          & makeClosure (compileBaseFun t)
          -- & write (next (trans-∈-⊆ this (++→⊆-l (lmr Γ)))) this
          & writeCtx2 {Γ₀ = [] ,, mr A} {Γ = lmr Γ} {Γ₁ = lmr As} this (skip (++→⊆-r _))
          & writeCtx {Γ₀ = _ :: _ :: []} this
          & call this

  in ret p
compileBaseFun {Γ} {As}(var x) =
  let p = init {Γ = lmr Γ ++ lmr As}
          & proj (trans-∈-⊆ (mr-∈ x) (++→⊆-r _))
          & writeCtx {Γ₀ = _ :: []} this
          & call this
  in ret p


module Test where
  t : [] ⊢2 (([] ,, ([] ⇉ NN)) ⇉ NN)
  t = lam (app (lam (var this)) (var this))

  te = compileVal t
  tee = eval te

  pro-1 pro-2 : [] ⊢2 (([] ,, ([] ⇉ NN) ,, ([] ⇉ NN)) ⇉ NN)
  pro-1 = lam (lam (var this))
  pro-2 = lam (lam (var (next this)))

  pro-1-c = compileBaseFun pro-1
  pro-1-e = evalFun pro-1-c -- λ e → fst (snd e) tt

  pro-2-c = compileBaseFun pro-2
  pro-2-e = evalFun pro-2-c -- λ e → fst e tt


