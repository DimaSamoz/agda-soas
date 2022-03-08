
open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength

-- Monoids with ⅀-algebra structure
module SOAS.Metatheory.Monoid {T : Set}
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ) (⅀:Str : Strength ⅀F)
  where

open import SOAS.Context
open import SOAS.Variable
open import SOAS.Construction.Structure as Structure
open import SOAS.Abstract.Hom

open import SOAS.Abstract.Monoid

open import SOAS.Coalgebraic.Map
open import SOAS.Coalgebraic.Monoid

open import SOAS.Metatheory.Algebra {T} ⅀F
open import SOAS.Metatheory.SynAlgebra {T} ⅀F

open Strength ⅀:Str

private
  variable
    Γ Δ : Ctx
    α : T

-- Family with compatible monoid and ⅀-algebra structure
record ΣMon (ℳ : Familyₛ) : Set where
  field
    ᵐ : Mon ℳ
    𝑎𝑙𝑔 : ⅀ ℳ ⇾̣ ℳ

  open Mon ᵐ public

  field
    μ⟨𝑎𝑙𝑔⟩ : {σ : Γ ~[ ℳ ]↝ Δ}(t : ⅀ ℳ α Γ)
          → μ (𝑎𝑙𝑔 t) σ ≡ 𝑎𝑙𝑔 (str ᴮ ℳ (⅀₁ μ t) σ)

  module Model {𝔛 : Familyₛ}(ω : 𝔛 ⇾̣ ℳ) where

    ᵃ : SynAlg 𝔛 ℳ
    ᵃ = record { 𝑎𝑙𝑔 = 𝑎𝑙𝑔 ; 𝑣𝑎𝑟 = η ; 𝑚𝑣𝑎𝑟 = μ ∘ ω }

record ΣMon⇒ {ℳ 𝒩 : Familyₛ}(ℳᴹ : ΣMon ℳ)(𝒩ᴹ : ΣMon 𝒩)
             (f : ℳ ⇾̣ 𝒩) : Set where
  private module ℳ = ΣMon ℳᴹ
  private module 𝒩 = ΣMon 𝒩ᴹ
  field
    ᵐ⇒ : Mon⇒ ℳ.ᵐ 𝒩.ᵐ f
    ⟨𝑎𝑙𝑔⟩ : {t : ⅀ ℳ α Γ} → f (ℳ.𝑎𝑙𝑔 t) ≡ 𝒩.𝑎𝑙𝑔 (⅀₁ f t)

  open Mon⇒ ᵐ⇒ public

-- Category of Σ-monoids
module ΣMonoidStructure = Structure 𝔽amiliesₛ ΣMon

ΣMonoidCatProps : ΣMonoidStructure.CategoryProps
ΣMonoidCatProps = record
  { IsHomomorphism = ΣMon⇒
  ; id-hom = λ {ℳ}{ℳᴹ} → record
    { ᵐ⇒ = AsMonoid⇒.ᵐ⇒ 𝕄on.id
    ; ⟨𝑎𝑙𝑔⟩ = cong (ΣMon.𝑎𝑙𝑔 ℳᴹ) (sym ⅀.identity)
    }
  ; comp-hom = λ{ {𝐸ˢ = 𝒪ᴹ} g f record { ᵐ⇒ = gᵐ⇒ ; ⟨𝑎𝑙𝑔⟩ = g⟨𝑎𝑙𝑔⟩ }
                      record { ᵐ⇒ = fᵐ⇒ ; ⟨𝑎𝑙𝑔⟩ = f⟨𝑎𝑙𝑔⟩ } → record
    { ᵐ⇒ = AsMonoid⇒.ᵐ⇒ ((g ⋉ gᵐ⇒) 𝕄on.∘ (f ⋉ fᵐ⇒))
    ; ⟨𝑎𝑙𝑔⟩ = trans (cong g f⟨𝑎𝑙𝑔⟩) (trans g⟨𝑎𝑙𝑔⟩
                   (cong (ΣMon.𝑎𝑙𝑔 𝒪ᴹ) (sym ⅀.homomorphism))) } }
  }

Σ𝕄onoids : Category 1ℓ 0ℓ 0ℓ
Σ𝕄onoids = ΣMonoidStructure.StructCat ΣMonoidCatProps

module Σ𝕄on = Category Σ𝕄onoids

ΣMonoid : Set₁
ΣMonoid = Σ𝕄on.Obj

ΣMonoid⇒ : ΣMonoid → ΣMonoid → Set
ΣMonoid⇒ = Σ𝕄on._⇒_

module FreeΣMonoid = ΣMonoidStructure.Free ΣMonoidCatProps
