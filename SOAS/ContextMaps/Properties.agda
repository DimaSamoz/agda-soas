
import SOAS.Families.Core

-- Various properties of context map operations
module SOAS.ContextMaps.Properties {T : Set}
  (open SOAS.Families.Core {T}) (𝒳 : Familyₛ) where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.ContextMaps.CategoryOfRenamings {T}
open import SOAS.ContextMaps.Combinators

open import Categories.Functor.Bifunctor
open import Categories.Object.Initial
open import Categories.Object.Coproduct
open import Categories.Category.Cocartesian
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (niHelper) renaming (refl to NI-refl)

private
  variable
    Γ Δ Θ Ξ : Ctx
    α : T

-- Copairing and injection
copair∘i₁ : {σ : Γ ~[ 𝒳 ]↝ Θ}{ς : Δ ~[ 𝒳 ]↝ Θ} (v : ℐ α Γ)
          → copair 𝒳 σ ς (∔.i₁ v) ≡ σ v
copair∘i₁ new = refl
copair∘i₁ {σ = σ} (old v) = copair∘i₁ {σ = σ ∘ old} v

copair∘i₂ : {σ : Γ ~[ 𝒳 ]↝ Θ}{ς : Δ ~[ 𝒳 ]↝ Θ} (v : ℐ α Δ)
          → copair 𝒳 σ ς (∔.i₂  {Γ} v) ≡ ς v
copair∘i₂ {Γ = ∅} v = refl
copair∘i₂ {Γ = α ∙ Γ} {σ = σ} v = copair∘i₂ {σ = σ ∘ old} v

-- Push function into copairing
f∘copair : (𝒳 {𝒴} : Familyₛ) (f : Θ ~[ 𝒳 ➔ 𝒴 ]↝ Ξ)(σ : Γ ~[ 𝒳 ]↝ Θ)(ς : Δ ~[ 𝒳 ]↝ Θ)
          (v : ℐ α (Γ ∔ Δ))
         → f (copair 𝒳 σ ς v) ≡ copair 𝒴 (f ∘ σ) (f ∘ ς) v
f∘copair {Γ = ∅} 𝒳 f σ ς v = refl
f∘copair {Γ = α ∙ Γ} 𝒳 f σ ς new = refl
f∘copair {Γ = α ∙ Γ} 𝒳 f σ ς (old v) = f∘copair 𝒳 f (σ ∘ old) ς v
