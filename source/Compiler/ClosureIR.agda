

module Compiler.ClosureIR where

open import Base.Prelude

-----------------------------------------------------
-- The base types
data BaseTy : 𝒰₀ where
  NN : BaseTy -- "natural numbers"


-----------------------------------------------------
-- A simple, typed lambda calculus

-- The types:
data Ty : 𝒰₀ where
  ι : BaseTy -> Ty
  _⇒_ : Ty -> Ty -> Ty

Ctx = List Ty

-- The terms:
-- We allow only well typed terms, the constructors mirror
-- the typing rules for LC
data _⊢_ : Ctx -> Ty -> 𝒰₀ where
  app : ∀{Γ A B} -> Γ ⊢ A ⇒ B -> Γ ⊢ A -> Γ ⊢ B
  lam : ∀{Γ A B} -> Γ ,, A ⊢ B -> Γ ⊢ A ⇒ B
  var : ∀{Γ A} -> A ∈ Γ -> Γ ⊢ A

infixr 50 _⊢_
infixr 70 _⇒_

-----------------------------------------------------
-- Another simple, typed lambda calculus
-- (but here, we use a different representation of types)


-- The types:
data UncurTy : 𝒰₀
-- They are represented as "uncurried" types, ie: they only ever have base types as targets
-- E.g.:
-- The type (NN ⇒ (NN ⇒ NN))
-- is now written as: ((([] ⇉ NN) :: ([] ⇉ NN) :: []) ⇉ NN)

-- The contexts:
UncurCtx = List UncurTy

-- The actual definition of types:
data UncurTy where
  _⇉_ : UncurCtx -> BaseTy -> UncurTy

infixl 40 _⇉_

-- The terms:
infixr 50 _⊢uc_
data _⊢uc_ : UncurCtx -> UncurTy -> 𝒰₀ where
  app : ∀{Γ A Bs B} -> Γ ⊢uc ((A :: Bs) ⇉ B) -> Γ ⊢uc A -> Γ ⊢uc (Bs ⇉ B)
  lam : ∀{Γ A Bs B} -> Γ ,, A ⊢uc (Bs ⇉ B) -> Γ ⊢uc ((A :: Bs) ⇉ B)
  var : ∀{Γ A} -> A ∈ Γ -> Γ ⊢uc A


normal→uc-Ctx : Ctx -> UncurCtx
normal→uc-Ty : Ty -> UncurTy

normal→uc-Ctx = map-List normal→uc-Ty

normal→uc-Ty (ι x) = [] ⇉ x
normal→uc-Ty (A ⇒ B) with normal→uc-Ty B
... | (Xs ⇉ X) = (normal→uc-Ty A :: Xs) ⇉ X

-- TODO: Create a function from usual lambda terms to UC lambda terms
-- normal→uc-Te : ∀{Γ A} -> Γ ⊢ A -> normal→uc-Ctx Γ ⊢uc normal→uc-Ty A
-- normal→uc-Te (app t s) = {!!}
-- normal→uc-Te (lam t) = {!!}
-- normal→uc-Te (var x) = {!!}


-----------------------------------------------------
-- The "Closure Intermediate Representation"

-- We now differentiate between computed and not yet computed values
-- For this, we define a new set of types (Cl[osure] Ty[pes]):
data ClTy : 𝒰₀
ClCtx = List ClTy

-- But inside of these, we also use types, which are just like UncurTy
-- TODO: Is this really necessary?
data ClUncurTy : 𝒰₀
data ClUncurTy where
  _⇉_ : ClCtx -> BaseTy -> ClUncurTy

-- The actual Closure Types:
data ClTy where
  ι : BaseTy -> ClTy
  Closure : ClUncurTy -> ClTy


-- A term in this IR is given by a sequence of commands, which, when given input data
-- of types as described in context Γ, produces data as required by context Δ
data CommandSeq : (Γ : ClCtx) -> (Δ : ClCtx) -> 𝒰₀

-- A command takes data in a context Γ, and produces a value of type A
data Command : (Γ : ClCtx) -> (A : ClTy) -> 𝒰₀

-- A function, similarly, produces a value in a context. This datatype currently only
-- is there for being more explicit about what is meant
data Function : ClCtx -> ClTy -> 𝒰₀

-- Def of a sequence of commands
data CommandSeq where
  -- an empty sequence:
  init : ∀{Γ} -> CommandSeq Γ Γ
  -- given a sequence, add a new value to the produced context, by executing a single command
  _&_ : ∀{Γ Δ A} -> CommandSeq Γ Δ -> Command Δ A -> CommandSeq Γ (Δ ,, A)

infixl 20 _&_

-- Def of command
data Command where
  -- If we have a value in our context, we can get that again as value
  proj : ∀{Γ A} -> A ∈ Γ -> Command Γ A

  -- Given a function ("definition"), we can create a closure, and take that as a value
  -- The closure, at first, has no "closured data"
  makeClosure : ∀{Γ Δ A} -> Function Γ (ι A) -> Command Δ (Closure (Γ ⇉ A))

  -- If we can produce a value (: A) which is needed by a closure, we can write it into it,
  -- producing a closure which needs less arguments
  write2 : ∀{Γ As A As2 B} -> A ∈ Γ -> (Closure ((As ++ (([] ,, A) ++ As2)) ⇉ B)) ∈ Γ -> Command Γ (Closure (As ++ As2 ⇉ B))

  -- if we have a closure, for which all arguments are given, we can execute it, to produce a
  -- value of its return type
  call : ∀{Γ A} -> (Closure ([] ⇉ A)) ∈ Γ -> Command Γ (ι A)

  -- Execute a sequence of commands, and get the last produced value
  inline : ∀{Γ Δ A} -> CommandSeq Γ (Δ ,, A) -> Command Γ A

  -- These are probably not strictly necessary, but the make writing chains of commands easier.
  -- If a command needs data from a context Γ, we can also execute it in an extended context Γ ++ Δ
  weak : ∀{Δ Γ A} -> Command Γ A -> Command (Γ ++ Δ) A
  weak1 : ∀{B Γ A} -> Command (Γ) A -> Command (Γ ,, B) A

-- A function is merely a seqence of commands
data Function where
  ret : ∀{Γ Δ A} -> CommandSeq Γ (Δ ,, A) -> Function Γ A


--------------------------------------------------------------------------------
-- Compiling the ⊢uc ("uncurried-type") terms to the ClosureIR
--------------------------------------------------------------------------------

-------------------------------------------------
-- Mapping the types

-- We need to map the uc types to cl types, as well as the contexts
uc→cl-Ctx : UncurCtx -> ClCtx

uc→cl : UncurTy -> ClTy
uc→cl (A ⇉ B) = Closure (uc→cl-Ctx A ⇉ B)

uc→cl-Ctx [] = []
uc→cl-Ctx (A :: As) = uc→cl A :: uc→cl-Ctx As

uc→cl-∈ : ∀{A Γ} -> A ∈ Γ -> uc→cl A ∈ uc→cl-Ctx Γ
uc→cl-∈ {x ⇉ x₁} {.(x ⇉ x₁) :: G} this = this
uc→cl-∈ {x ⇉ x₁} {x₂ :: G} (next i) = next (uc→cl-∈ i)


-------------------------------------------------
-- Additional command shortcuts

-- We define some shortcuts for the "write2" command
write : ∀{Γ A As B} -> A ∈ Γ -> (Closure ((As ,, A) ⇉ B)) ∈ Γ -> Command Γ (Closure (As ⇉ B))
write {Γ} {A} {As} {B} i c = write2 {As = []} {A = A} {As2 = As} {B = B} i c

-- Also, for writing more values at once
writeCtx2 : ∀{Γ₀ Γ Γ₁ Δ A} -> Closure (Γ₀ ++ (Γ ++ Γ₁) ⇉ A) ∈ Δ -> Γ ⊆ Δ -> Command Δ (Closure ((Γ₀ ++ Γ₁) ⇉ A))
writeCtx2 {G0} {[]} {G1} {D} c g = proj c
writeCtx2 {G0} {x :: G} {G1} {D} {A} c g =
  let qq = write2 {Γ = D} {As = G0} {A = x} {As2 = (G ++ G1)} {B = A} (trans-∈-⊆ this g) c
      p = init {Γ = D}
          & qq
          & writeCtx2 {Γ₀ = G0} {Γ = G} {Γ₁ = G1} this (trans-⊆ (skip refl) (trans-⊆ g (skip refl)))
  in inline p

-- Here as well
writeCtx : ∀{Γ₀ Γ Ξ A} -> Closure (Ξ ⇉ A) ∈ Γ₀ -> Command (Γ₀ ++ (Γ ++ Ξ)) (Closure ([] ⇉ A))
writeCtx {Γ₀} {Γ} {Ξ} {A} c with writeCtx2 {Γ₀ = []} {Γ = Ξ} {Γ₁ = []} {Δ = Γ₀ ++ (Γ ++ Ξ)}
... | ff rewrite List-++-[] Ξ = ff (trans-∈-⊆ c (++→⊆-r _)) (trans-⊆ (++→⊆-l Γ) (++→⊆-l Γ₀))


-------------------------------------------------
-- The actual translation/compilation

-- We have to versions of the compilation function

-- The first, compiles a term into a command for producing exactly a value of type A in a context Γ
compileCommand : ∀{Γ A} -> (t : Γ ⊢uc (A)) -> Command (uc→cl-Ctx Γ) (uc→cl A)

-- The second, compiles a term into a function definition. But without regards to the actual
-- type of the term, it compiles it into a function with an as much as possible uncurried type.
-- I.e., a term [ℕ] ⊢ ℕ ⇒ ℕ is compiled to [ℕ , ℕ] ⊢ ℕ
compileFunction : ∀{Γ As A} -> (t : Γ ⊢uc (As ⇉ A)) -> Function (uc→cl-Ctx Γ ++ uc→cl-Ctx As) (ι A)


-- The def
-- A term is translated into a sequence of commands (each of which adds a new value to the context,
-- and the last is taken as result value)
compileCommand {Γ} {(_ ⇉ _)} (app t s) =
  let p = init {Γ = uc→cl-Ctx Γ}
          & compileCommand t
          & weak1 (compileCommand s)
          & write this (next this)
  in inline p
compileCommand {Γ} {.((_ :: _) ⇉ _)} (lam t) =
  let p = init {Γ = uc→cl-Ctx (Γ)}
           & makeClosure (compileFunction t)
           & writeCtx2 {Γ₀ = [] ,, _} this (skip refl)

  in inline p
compileCommand {Γ} {A} (var x) = proj (uc→cl-∈ x)


-- The def
compileFunction {Γ} {As} (app {A = (Xs ⇉ X)} t s) =
  let p = init {uc→cl-Ctx Γ ++ uc→cl-Ctx As}
          & weak (compileCommand t)
          & weak1 (weak (compileCommand s))
          & write (this) (next this)
          & writeCtx {Γ₀ = _ :: _ :: _ :: []} {Γ = uc→cl-Ctx Γ} {Ξ = uc→cl-Ctx As} this
          & call this
  in ret p
compileFunction {Γ} {As ,, A} (lam {B = B} t) =
  let t2 = compileFunction t
      p = init {uc→cl-Ctx Γ ++ (uc→cl A :: uc→cl-Ctx As)}
          & makeClosure (compileFunction t)
          & writeCtx2 {Γ₀ = [] ,, uc→cl A} {Γ = uc→cl-Ctx Γ} {Γ₁ = uc→cl-Ctx As} this (skip (++→⊆-r _))
          & writeCtx {Γ₀ = _ :: _ :: []} this
          & call this

  in ret p
compileFunction {Γ} {As}(var x) =
  let p = init {Γ = uc→cl-Ctx Γ ++ uc→cl-Ctx As}
          & proj (trans-∈-⊆ (uc→cl-∈ x) (++→⊆-r _))
          & writeCtx {Γ₀ = _ :: []} this
          & call this
  in ret p


--------------------------------------------------------------------------------
-- Interpreting the ClosureIR back into Agda terms
--------------------------------------------------------------------------------

-- Interpretation of Contexts
CtxInt : ClCtx -> 𝒰₀

-- Interpretation of base types
BaseTyInt : BaseTy -> 𝒰₀
BaseTyInt (NN) = ℕ

-- Interpretation of closure types
ClTyInt : ClTy -> 𝒰₀
ClTyInt (ι a) = BaseTyInt a
ClTyInt (Closure (x ⇉ y)) = CtxInt x -> BaseTyInt y

CtxInt [] = ⊤
CtxInt (x :: G) = ClTyInt x × CtxInt G


-- Interpretation of the `proj` command
projInt : ∀{Γ A} -> A ∈ Γ -> CtxInt Γ -> ClTyInt A
projInt this (x , _) = x
projInt (next i) (_ , e) = projInt i e

-- Interpretation of a command
-- A (Command Γ A) is interpreted into a function from ⟦ Γ ⟧ to ⟦ A ⟧
eval : ∀{Γ A} -> Command Γ A -> CtxInt Γ -> ClTyInt A

-- Interpretation of a command sequence
evalSeq : ∀{Γ Δ} -> CommandSeq Γ Δ -> CtxInt Γ -> CtxInt Δ
evalSeq init x = x
evalSeq (s & x) e = let sv = evalSeq s e
                        xv = eval x sv
                    in xv , sv

evalFun : ∀{Γ A} -> Function Γ A -> CtxInt Γ -> ClTyInt A
evalFun (ret x) e = let (r , _) = evalSeq x e
                    in r

-- Interpreting `weak`
evalWeak : ∀{Γ Δ} -> CtxInt (Γ ++ Δ) -> CtxInt Γ
evalWeak {[]} {D} e = tt
evalWeak {x :: G} {D} (v1 , vr) = v1 , evalWeak vr

-- Interpreting `write`
splice : ∀{Γ A Δ} -> CtxInt (Γ ++ Δ) -> ClTyInt A -> CtxInt (Γ ++ (A :: Δ))
splice {[]} {A} {D} e a = a , e
splice {G0 :: G} {A} {D} (x , e) a = x , splice e a

eval (call x) e = projInt x e tt
eval (makeClosure f) _ e2 = evalFun f e2
eval (weak {Δ = D} {Γ = G} v) e = eval v (evalWeak e)
eval (weak1 v) (_ , e) = eval v e
eval (inline x) e = evalSeq x e .fst
eval (write2 t s) e e2 =
  let vt = projInt t e
      vs = projInt s e
  in vs (splice e2 vt)
eval (proj x) e = projInt x e



--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

module Test where
  -- This is: λ y -> (λ x -> x) y
  t : [] ⊢uc (([] ,, ([] ⇉ NN)) ⇉ NN)
  t = lam (app (lam (var this)) (var this))

  te = compileCommand t
  tee = eval te -- Normalizes to: λ e e2 → fst e2 tt

  pro-1 pro-2 : [] ⊢uc (([] ,, ([] ⇉ NN) ,, ([] ⇉ NN)) ⇉ NN)
  pro-1 = lam (lam (var this))        -- λ x y -> y
  pro-2 = lam (lam (var (next this))) -- λ x y -> x

  pro-1-c = compileFunction pro-1
  pro-1-e = evalFun pro-1-c -- Normalizes to: λ e → fst (snd e) tt

  pro-2-c = compileFunction pro-2
  pro-2-e = evalFun pro-2-c -- Normalizes to: λ e → fst e tt


