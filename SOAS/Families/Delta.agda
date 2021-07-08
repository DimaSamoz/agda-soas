
-- Context extension of presheaves
module SOAS.Families.Delta {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Sorting
open import SOAS.Construction.Structure
open import SOAS.Families.Core {T}


-- | General context extension by a context Θ

module Unsorted where

  -- Concatenate Θ to the context of a family
  δ : Ctx → Family → Family
  δ Θ X Γ = X (Θ ∔ Γ)

  δF : Ctx → Functor 𝔽amilies 𝔽amilies
  δF Θ = record { F₀ = δ Θ ; F₁ = λ f → f ; identity = refl
                 ; homomorphism = refl ; F-resp-≈ = λ z → z }

  -- | Context extension by a single type τ, a special case of δ with ⌊ τ ⌋
  δ₁ : T → Family → Family
  δ₁ τ = δ ⌈ τ ⌋

  δ₁F_ : T → Functor 𝔽amilies 𝔽amilies
  δ₁F τ = δF ⌈ τ ⌋

private
  variable
    Γ Δ : Ctx
    α : T

module Sorted where
  -- Concatenate Θ to the context of a family
  δ : Ctx → Familyₛ → Familyₛ
  δ Θ 𝒳 α Γ = 𝒳 α (Θ ∔ Γ)


  δF : Ctx → Functor 𝔽amiliesₛ 𝔽amiliesₛ
  δF Θ = record { F₀ = δ Θ ; F₁ = λ f → f ; identity = refl
                 ; homomorphism = refl ; F-resp-≈ = λ z → z }

  -- | Context extension by a single type τ, a special case of δ with ⌊ τ ⌋
  δ₁ : T → Familyₛ → Familyₛ
  δ₁ τ = δ ⌈ τ ⌋

  δ₁F_ : T → Functor 𝔽amiliesₛ 𝔽amiliesₛ
  δ₁F τ = δF ⌈ τ ⌋
