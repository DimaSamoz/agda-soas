
open import SOAS.Common

{-
Framework for constructing categories of objects with extra structure.
The definitions required to construct a category is:
* the category of carrier objects (e.g. sets, presheaves, etc.)
* the extra operations and laws that the carrier objects are equipped with
* the preservation properties of morphisms between the structures
* proofs that the identities and composition of the carrier category preserve
  the extra structure
-}

module SOAS.Construction.Structure
  (CarrierCat : Category 1ℓ 0ℓ 0ℓ)
  (HasStruct : Category.Obj CarrierCat → Set) where

private module ℂ = Category CarrierCat

-- The carrier of the structure, e.g. sets, presheaves, etc.
Carrier : Set₁
Carrier = ℂ.Obj

infix 1 _⋉_

-- Objects in the category for the structure: a carrier object together with
-- the algebraic structure
record Object : Set₁ where
  constructor _⋉_
  field
    𝐶 : Carrier
    ˢ : HasStruct 𝐶

open Object public

-- Properties of the morphisms between two objects, usually concerning
-- the preservation of the extra operations
MorphismProps : Set₁
MorphismProps = {𝐶₁ 𝐶₂ : Carrier}
              → HasStruct 𝐶₁
              → HasStruct 𝐶₂
              → CarrierCat [ 𝐶₁ , 𝐶₂ ] → Set

-- Morphisms in the category for the algebraic structure: an underlying
-- morphism with preservation properties of the extra structure
record Morphism (IsHomomorphism : MorphismProps) (O₁ O₂ : Object) : Set where
  constructor _⋉_
  field
    𝑓   : CarrierCat [ 𝐶 O₁ , 𝐶 O₂ ]
    ˢ⇒ : IsHomomorphism (ˢ O₁)(ˢ O₂) 𝑓

open Morphism public

-- Properties required to turn the objects and morphisms into a category; namely
-- that the identity and composition in the carrier category are homomorphisms
record CategoryProps : Set₁ where
  field
    IsHomomorphism  : MorphismProps
    id-hom   : {𝐶 : Carrier}{𝐶ˢ : HasStruct 𝐶} → IsHomomorphism 𝐶ˢ 𝐶ˢ ℂ.id
    comp-hom : {𝐶 𝐷 𝐸 : Carrier}
               {𝐶ˢ : HasStruct 𝐶}{𝐷ˢ : HasStruct 𝐷}{𝐸ˢ : HasStruct 𝐸} →
               (𝑔 : CarrierCat [ 𝐷 , 𝐸 ])(𝑓 : CarrierCat [ 𝐶 , 𝐷 ]) →
               (𝑔ʰ : IsHomomorphism 𝐷ˢ 𝐸ˢ 𝑔)(𝑓ʰ : IsHomomorphism 𝐶ˢ 𝐷ˢ 𝑓) →
               IsHomomorphism 𝐶ˢ 𝐸ˢ (𝑔 ℂ.∘ 𝑓)

module _ (P : CategoryProps) where
  open CategoryProps P

  -- Category generated from the algebraic structure
  StructCat : Category 1ℓ 0ℓ 0ℓ
  StructCat = categoryHelper (record
    { Obj = Object
    ; _⇒_ = Morphism IsHomomorphism
    ; _≈_ = λ g₁ g₂ → 𝑓 g₁ ℂ.≈ 𝑓 g₂
    ; id = ℂ.id ⋉ id-hom
    ; _∘_ = λ{ (𝑔 ⋉ 𝑔ˢ⇒) (𝑓 ⋉ 𝑓ˢ⇒) → (𝑔 ℂ.∘ 𝑓) ⋉ (comp-hom 𝑔 𝑓 𝑔ˢ⇒ 𝑓ˢ⇒)}
    ; assoc = ℂ.assoc
    ; identityˡ = ℂ.identityˡ
    ; identityʳ = ℂ.identityʳ
    ; equiv = record { refl = ℂ.Equiv.refl ; sym = ℂ.Equiv.sym ; trans = ℂ.Equiv.trans }
    ; ∘-resp-≈ = ℂ.∘-resp-≈
    })

  -- Forget the structure of a carrier object
  Forget :  Object → Carrier
  Forget (𝐶 ⋉ _) = 𝐶

  -- Forgetful functor from the structure category to the carrier category
  ForgetF : Functor StructCat CarrierCat
  ForgetF = record
    { F₀ = Forget
    ; F₁ = λ (𝑓 ⋉ _) → 𝑓
    ; identity = ℂ.Equiv.refl
    ; homomorphism = ℂ.Equiv.refl
    ; F-resp-≈ = λ x → x
    }
    where
    open ≡-Reasoning

  -- Free constructions with respect to the forgetful functor
  module Free where
    open import SOAS.Construction.Free ForgetF public
