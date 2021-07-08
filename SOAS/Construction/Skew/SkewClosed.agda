{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- Skew closed structure on a category
module SOAS.Construction.Skew.SkewClosed {o ℓ e} (C : Category o ℓ e) where

private
  module C = Category C
  open C
  variable
    A B X X′ Y Y′ Z Z′ U ℐ : Obj
    f g : A ⇒ B

  open Commutation C

open import Level
open import Data.Product using (Σ; _,_)
open import Function.Equality using (_⟶_)
open import Function.Inverse using (_InverseOf_; Inverse)

open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Construction.Constant
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation.Dinatural

record SkewClosed : Set (levelOfTerm C) where
  field
    -- internal hom
    [-,-] : Bifunctor C.op C C
    unit  : Obj

  [_,-] : Obj → Functor C C
  [_,-] = appˡ [-,-]

  [-,_] : Obj → Functor C.op C
  [-,_] = appʳ [-,-]

  module [-,-] = Functor [-,-]

  [_,_]₀ : Obj → Obj → Obj
  [ X , Y ]₀ = [-,-].F₀ (X , Y)

  [_,_]₁ : A ⇒ B → X ⇒ Y → [ B , X ]₀ ⇒ [ A , Y ]₀
  [ f , g ]₁ = [-,-].F₁ (f , g)

  field
    -- i
    identity : NaturalTransformation [ unit ,-] idF
    -- j
    diagonal : Extranaturalʳ unit [-,-]

  module identity = NaturalTransformation identity
  module diagonal = DinaturalTransformation diagonal

  [[X,-],[X,-]] : Obj → Bifunctor C.op C C
  [[X,-],[X,-]] X = [-,-] ∘F (Functor.op [ X ,-] ⁂ [ X ,-])

  [[-,Y],[-,Z]] : Obj → Obj → Bifunctor C C.op C
  [[-,Y],[-,Z]] Y Z = [-,-] ∘F ((Functor.op [-, Y ]) ⁂ [-, Z ])

  -- L needs to be natural in Y and Z.
  -- it is better to spell out the conditions and then prove that indeed
  -- the naturality conditions hold.
  field
    L : ∀ X Y Z → [ Y , Z ]₀ ⇒ [ [ X , Y ]₀ , [ X , Z ]₀ ]₀
    L-commute : [ [ Y , Z ]₀ ⇒  [ [ X , Y′ ]₀ , [ X , Z′ ]₀ ]₀ ]⟨
                  [ f , g ]₁                          ⇒⟨ [ Y′ , Z′ ]₀ ⟩
                  L X Y′ Z′
                ≈ L X Y Z                             ⇒⟨ [ [ X , Y ]₀ , [ X , Z ]₀ ]₀ ⟩
                  [ [ C.id , f ]₁ , [ C.id , g ]₁ ]₁
                ⟩

  L-natural : NaturalTransformation [-,-] ([[X,-],[X,-]] X)
  L-natural {X} = ntHelper record
    { η       = λ where
      (Y , Z) → L X Y Z
    ; commute = λ _ → L-commute
    }

  module L-natural {X}     = NaturalTransformation (L-natural {X})

  -- other required diagrams
  field
    Lj≈j : [ unit ⇒ [ [ X , Y ]₀ , [ X , Y ]₀ ]₀ ]⟨
             diagonal.α  Y                  ⇒⟨ [ Y , Y ]₀ ⟩
             L X Y Y
           ≈ diagonal.α [ X , Y ]₀
           ⟩
    ijL≈id : [ [ X , Y ]₀ ⇒ [ X , Y ]₀ ]⟨
             L X X Y                   ⇒⟨ [ [ X , X ]₀ , [ X , Y ]₀ ]₀ ⟩
             [ diagonal.α X , C.id ]₁  ⇒⟨ [ unit , [ X , Y ]₀ ]₀ ⟩
             identity.η [ X , Y ]₀
           ≈ C.id
           ⟩
    iL≈i : [ [ Y , Z ]₀ ⇒ [ [ unit , Y ]₀ , Z ]₀ ]⟨
             L unit Y Z                ⇒⟨ [ [ unit , Y ]₀ , [ unit , Z ]₀ ]₀ ⟩
             [ C.id , identity.η Z ]₁
           ≈ [ identity.η Y , C.id ]₁
           ⟩

    ij≈id : [ unit ⇒ unit ]⟨
             diagonal.α unit    ⇒⟨ [ unit , unit ]₀ ⟩
             identity.η unit
           ≈ C.id
           ⟩

    pentagon : [ [ U , ℐ ]₀ ⇒ [ [ Y , U ]₀ , [ [ X , Y ]₀ , [ X , ℐ ]₀ ]₀ ]₀ ]⟨
                 L X U ℐ                            ⇒⟨ [ [ X , U ]₀ , [ X , ℐ ]₀ ]₀ ⟩
                 L [ X , Y ]₀ [ X , U ]₀ [ X , ℐ ]₀ ⇒⟨ [ [ [ X , Y ]₀ , [ X , U ]₀ ]₀ , [ [ X , Y ]₀ , [ X , ℐ ]₀ ]₀ ]₀ ⟩
                 [ L X Y U , C.id ]₁
               ≈ L Y U ℐ                            ⇒⟨ [ [ Y , U ]₀ , [ Y , ℐ ]₀ ]₀ ⟩
                 [ C.id , L X Y ℐ ]₁
               ⟩
