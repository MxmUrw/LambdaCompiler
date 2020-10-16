
module Compiler.JmpIR where

open import Base.Prelude


List : 𝒰 ℓ -> 𝒰 ℓ
List A = ∑ Vec A

record MGraph : 𝒰₁ where
  field
    Obj : 𝒰₀
    Op : List Obj -> Obj -> 𝒰₀

open MGraph

data FreeMCatHom {G : MGraph} : (A : List (Obj G)) -> (B : Obj G) -> 𝒰₀ where
  id : {A : Obj G} -> FreeMCatHom (_ , A ∷ []) A
  op : ∀{A B} -> (o : Op G A B) -> FreeMCatHom A B
  -- comp : {A B C : Obj G} -> (f : FreeMCatHom {G} A B) -> (g : FreeMCatHom {G} B C) -> FreeMCatHom A C

FunctionSignature : (Obj : 𝒰₀) -> 𝒰₀
FunctionSignature Obj = List Obj × Obj

ProgramSignature : (Obj : 𝒰₀) -> 𝒰₀
ProgramSignature Obj = List (FunctionSignature Obj)

record MGraphExtension (G : MGraph) : 𝒰₁ where
  field Obj₂ : 𝒰₀
        Op₂ : List (Obj G) -> List Obj₂ -> (Obj G + Obj₂) -> 𝒰₀

open MGraphExtension

split : ∀{A B : 𝒰 ℓ} -> (List (A + B)) -> (List A) × (List B)
split (_ , []) = (_ , []) , (_ , [])
split (_ , x ∷ l) with x | split (_ , l)
... | (left a)  | ((_ , la) , (_ , lb)) = ((_ , a ∷ la) , (_ , lb))
... | (right b) | ((_ , la) , (_ , lb)) = ((_ , la)     , (_ , b ∷ lb))

_+>_ : (G : MGraph) -> (GE : MGraphExtension G) -> MGraph
Obj (G +> GE) = Obj G + Obj₂ GE
Op (G +> GE) As (left B) = let A₁s , A₂s = split As
                           in Op G A₁s B + Op₂ GE A₁s A₂s (left B) -- check for As to be all left, then call Op on them
Op (G +> GE) As (right B) = let A₁s , A₂s = split As
                            in Op₂ GE A₁s A₂s (right B) -- check for As to be all left, then call Op on them

data PointerObj (Obj : 𝒰₀) : 𝒰₀ where
  Val : Obj -> PointerObj Obj
  Pointer : PointerObj Obj -> PointerObj Obj

pointerExtension : (G : MGraph) -> MGraphExtension G
Obj₂ (pointerExtension G) = PointerObj (Obj G)
Op₂ (pointerExtension G) = {!!}

callExtension : (G : MGraph) -> (ProgramSignature (Obj G)) -> MGraphExtension G
Obj₂ (callExtension G σ) = ⊥
Op₂ (callExtension G σ) = {!!} -- add a hom for every function signature


BlockDefinitions : (Obj : 𝒰₀) -> FunctionSignature Obj -> 𝒰₀
BlockDefinitions Obj F = {!!} × (List Obj × List Obj) × {!!}

Blocks : {Obj : 𝒰₀} -> (F : FunctionSignature Obj) -> (B : BlockDefinitions Obj F) -> 𝒰₀
Blocks F (_ , (s , t) , _) = {!!}

jmpExtension : (G : MGraph) -> (F : FunctionSignature (Obj G)) -> (BlockDefinitions (Obj G) F) -> MGraphExtension G
jmpExtension G = {!!}

record Function (G : MGraph) (GE : MGraphExtension G) (F : FunctionSignature (Obj G)) : 𝒰₀ where
  field blockSigs : BlockDefinitions _ F
        blocks : Blocks F blockSigs

record Program (G : MGraph) : 𝒰₀ where
  field functionSigs : ProgramSignature (Obj G)
        functions : ∀{i} -> Function G (callExtension G functionSigs) (lookup (functionSigs .snd) i)



