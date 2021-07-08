
-- Categories with objects parameterised by a sort
module SOAS.Sorting {T : Set} where

open import SOAS.Common

import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.CartesianClosed as CCC
open import Categories.Category.Cocartesian
open import Categories.Category.BicartesianClosed
import Categories.Category.Monoidal as Monoidal
import Categories.Category.Monoidal.Closed as MonClosed
open import Categories.Object.Product
open import Categories.Functor.Bifunctor

-- Add sorting to a set
Sorted : Set₁ → Set₁
Sorted Obj = T → Obj

-- Lift a function on Obj to one on sorted Obj
sorted : {O₁ O₂ : Set₁} → (O₁ → O₂) → Sorted O₁ → Sorted O₂
sorted f 𝒳 τ = f (𝒳 τ)

-- Lift a binary operation on Obj to one on sorted Obj
sorted₂ : {O₁ O₂ O₃ : Set₁} → (O₁ → O₂ → O₃)
                            → Sorted O₁ → Sorted O₂ → Sorted O₃
sorted₂ op 𝒳 𝒴 τ = op (𝒳 τ) (𝒴 τ)

sortedᵣ : {O₁ O₂ O₃ : Set₁} → (O₁ → O₂ → O₃)
                            → O₁ → Sorted O₂ → Sorted O₃
sortedᵣ op X 𝒴 τ = op X (𝒴 τ)

sortedₗ : {O₁ O₂ O₃ : Set₁} → (O₁ → O₂ → O₃)
                           → Sorted O₁ → O₂ → Sorted O₃
sortedₗ op 𝒳 Y τ = op (𝒳 τ) Y

-- Turn a category into a sorted category
𝕊orted : Category 1ℓ 0ℓ 0ℓ → Category 1ℓ 0ℓ 0ℓ
𝕊orted Cat = categoryHelper (record
  { Obj = Sorted Obj
  ; _⇒_ = λ A B → ∀{τ : T} → A τ ⇒ B τ
  ; _≈_ = λ f g → ∀{α : T} → f {α} ≈ g {α}
  ; id = id Cat
  ; _∘_ = λ g f → Category._∘_ Cat g f
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = record { refl = E.refl equiv ; sym = λ p → E.sym equiv p
                   ; trans = λ p q → E.trans equiv p q }
  ; ∘-resp-≈ = λ p q → ∘-resp-≈ p q
  })
  where
  open Category Cat
  open import Relation.Binary.Structures renaming (IsEquivalence to E)

-- Lift functors to functors between sorted categories
𝕊orted-Functor : {ℂ 𝔻 : Category 1ℓ 0ℓ 0ℓ} → Functor ℂ 𝔻 → Functor (𝕊orted ℂ) (𝕊orted 𝔻)
𝕊orted-Functor F = record
  { F₀ = λ X τ → Functor.₀ F (X τ)
  ; F₁ = λ f → Functor.₁ F f
  ; identity = Functor.identity F
  ; homomorphism = Functor.homomorphism F
  ; F-resp-≈ = λ z → Functor.F-resp-≈ F z
  }

-- Lift bifunctors to bifunctors between sorted categories
𝕊orted-Bifunctor : {ℂ 𝔻 𝔼 : Category 1ℓ 0ℓ 0ℓ} → Bifunctor ℂ 𝔻 𝔼 → Bifunctor (𝕊orted ℂ) (𝕊orted 𝔻) (𝕊orted 𝔼)
𝕊orted-Bifunctor F = record
  { F₀ = λ{ (X , Y) τ → Functor.₀ F (X τ , Y τ)}
  ; F₁ = λ{ (f , g) → Functor.₁ F (f , g)}
  ; identity = Functor.identity F
  ; homomorphism = Functor.homomorphism F
  ; F-resp-≈ = λ{ (p , q) → Functor.F-resp-≈ F (p , q)}
  }


private
  variable C : Category 1ℓ 0ℓ 0ℓ

-- A sorted CCC is itself a CCC
𝕊orted-CanCCC : Canonical.CartesianClosed C
              → Canonical.CartesianClosed (𝕊orted C)
𝕊orted-CanCCC CCC = record
  { ⊤ = λ τ → 𝓒.terminal.⊤
  ; _×_ = λ A B τ → (A τ) 𝓒.× (B τ)
  ; ! = 𝓒.terminal.!
  ; π₁ = 𝓒.π₁
  ; π₂ = 𝓒.π₂
  ; ⟨_,_⟩ = λ f g → 𝓒.⟨ f , g ⟩
  ; !-unique = λ f → 𝓒.terminal.!-unique f
  ; π₁-comp = 𝓒.π₁-comp
  ; π₂-comp = 𝓒.π₂-comp
  ; ⟨,⟩-unique = λ p₁ p₂ → 𝓒.⟨,⟩-unique p₁ p₂
  ; _^_ = λ B A τ → B τ 𝓒.^ A τ
  ; eval = 𝓒.eval
  ; curry = λ f → 𝓒.curry f
  ; eval-comp = 𝓒.eval-comp
  ; curry-resp-≈ = λ p → 𝓒.curry-resp-≈ p
  ; curry-unique = λ p → 𝓒.curry-unique p
  } where private module 𝓒 = Canonical.CartesianClosed CCC


-- A sorted co-Cartesian category is co-Cartesian
𝕊orted-Cocartesian : Cocartesian C
                   → Cocartesian (𝕊orted C)
𝕊orted-Cocartesian Cocart = record
  { initial = record
    { ⊥ = λ τ → 𝓒.⊥ ; ⊥-is-initial = record
      { ! = 𝓒.initial.! ; !-unique = λ f → 𝓒.initial.!-unique f } }
  ; coproducts = record { coproduct = λ {A}{B} → record
    { A+B = λ τ → 𝓒.coproduct.A+B {A τ}{B τ}
    ; i₁ = 𝓒.i₁
    ; i₂ = 𝓒.i₂
    ; [_,_] = λ f g → 𝓒.[ f , g ]
    ; inject₁ = 𝓒.inject₁
    ; inject₂ = 𝓒.inject₂
    ; unique = λ p₁ p₂ → 𝓒.coproduct.unique p₁ p₂
    } }
  } where private module 𝓒 = Cocartesian Cocart

-- A sorted bi-Cartesian closed category is itself bi-Cartesian closed
𝕊orted-BCCC : BicartesianClosed C
            → BicartesianClosed (𝕊orted C)
𝕊orted-BCCC BCCC = record
  { cartesianClosed = fromCanonical _ (𝕊orted-CanCCC (toCanonical _ cartesianClosed))
  ; cocartesian = 𝕊orted-Cocartesian cocartesian
  }
  where
  open BicartesianClosed BCCC
  open Canonical.Equivalence

-- A sorted monoidal category is itself monoidal
𝕊orted-Monoidal : Monoidal.Monoidal C
                → Monoidal.Monoidal (𝕊orted C)
𝕊orted-Monoidal {C} Mon = record
  { ⊗ = record
    { F₀ = λ{ (X , Y) τ → X τ 𝓒.⊗₀ Y τ }
    ; F₁ = λ{ (f , g) → f 𝓒.⊗₁ g}
    ; identity = Functor.identity 𝓒.⊗
    ; homomorphism = Functor.homomorphism 𝓒.⊗
    ; F-resp-≈ = λ{ (p₁ , p₂) {α} → Functor.F-resp-≈ 𝓒.⊗ (p₁ , p₂) }
    }
  ; unit = λ τ → 𝓒.unit
  ; unitorˡ = record { from = λ {τ} → 𝓒.unitorˡ.from ; to = 𝓒.unitorˡ.to
                     ; iso = record { isoˡ = Iso.isoˡ 𝓒.unitorˡ.iso ; isoʳ = Iso.isoʳ 𝓒.unitorˡ.iso } }
  ; unitorʳ = record { from = λ {τ} → 𝓒.unitorʳ.from ; to = 𝓒.unitorʳ.to
                     ; iso = record { isoˡ = Iso.isoˡ 𝓒.unitorʳ.iso ; isoʳ = Iso.isoʳ 𝓒.unitorʳ.iso } }
  ; associator = record { from = λ {τ} → 𝓒.associator.from ; to = 𝓒.associator.to
                        ; iso = record { isoˡ = Iso.isoˡ 𝓒.associator.iso ; isoʳ = Iso.isoʳ 𝓒.associator.iso } }
  ; unitorˡ-commute-from = 𝓒.unitorˡ-commute-from
  ; unitorˡ-commute-to = 𝓒.unitorˡ-commute-to
  ; unitorʳ-commute-from = 𝓒.unitorʳ-commute-from
  ; unitorʳ-commute-to = 𝓒.unitorʳ-commute-to
  ; assoc-commute-from = 𝓒.assoc-commute-from
  ; assoc-commute-to = 𝓒.assoc-commute-to
  ; triangle = 𝓒.triangle
  ; pentagon = 𝓒.pentagon
  }
  where
  private module 𝓒 = Monoidal.Monoidal Mon
  open import Categories.Morphism C

-- A sorted monoidal closed category is itself monoidal closed
𝕊orted-MonClosed : {Mon : Monoidal.Monoidal C}
                 → MonClosed.Closed Mon
                 → MonClosed.Closed (𝕊orted-Monoidal Mon)
𝕊orted-MonClosed {Mon} Cl = record
  { [-,-] = record
    { F₀ = λ (X , Y) τ → 𝓒.[ X τ , Y τ ]₀
    ; F₁ = λ (f , g) → 𝓒.[ f , g ]₁
    ; identity = λ {A} {α} → Functor.identity 𝓒.[-,-]
    ; homomorphism = Functor.homomorphism 𝓒.[-,-]
    ; F-resp-≈ = λ{ (p₁ , p₂) {α} → Functor.F-resp-≈ 𝓒.[-,-] (p₁ , p₂) }
    }
  ; adjoint = record
    { unit = ntHelper record
      { η = λ X {τ} → NT.η 𝓒.adjoint.unit (X τ)
      ; commute = λ f → NT.commute 𝓒.adjoint.unit f
      }
    ; counit = ntHelper record
      { η = λ X {τ} → NT.η 𝓒.adjoint.counit (X τ)
      ; commute = λ f → NT.commute 𝓒.adjoint.counit f
      }
    ; zig = 𝓒.adjoint.zig
    ; zag = 𝓒.adjoint.zag
    }
  ; mate = λ f → record { commute₁ = 𝓒.mate.commute₁ f ; commute₂ = 𝓒.mate.commute₂ f }
  } where private module 𝓒 = MonClosed.Closed Cl
