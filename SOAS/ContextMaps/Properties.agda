
import SOAS.Families.Core

-- Various properties of context map operations
module SOAS.ContextMaps.Properties {T : Set}
  (open SOAS.Families.Core {T}) (𝒳 : Familyₛ) where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.ContextMaps.CategoryOfRenamings {T}
-- open import SOAS.ContextMaps.CategoryOfSubstitutions {T}
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

copair∘i₁ : {σ : Γ ~[ 𝒳 ]↝ Θ}{ς : Δ ~[ 𝒳 ]↝ Θ} (v : ℐ α Γ)
          → copair 𝒳 σ ς (∔.i₁ v) ≡ σ v
copair∘i₁ new = refl
copair∘i₁ {σ = σ} (old v) = copair∘i₁ {σ = σ ∘ old} v

copair∘i₂ : {σ : Γ ~[ 𝒳 ]↝ Θ}{ς : Δ ~[ 𝒳 ]↝ Θ} (v : ℐ α Δ)
          → copair 𝒳 σ ς (∔.i₂  {Γ} v) ≡ ς v
copair∘i₂ {Γ = ∅} v = refl
copair∘i₂ {Γ = α ∙ Γ} {σ = σ} v = copair∘i₂ {σ = σ ∘ old} v

f∘copair : (𝒳 {𝒴} : Familyₛ) (f : Θ ~[ 𝒳 ➔ 𝒴 ]↝ Ξ)(σ : Γ ~[ 𝒳 ]↝ Θ)(ς : Δ ~[ 𝒳 ]↝ Θ)
          (v : ℐ α (Γ ∔ Δ))
         → f (copair 𝒳 σ ς v) ≡ copair 𝒴 (f ∘ σ) (f ∘ ς) v
f∘copair {Γ = ∅} 𝒳 f σ ς v = refl
f∘copair {Γ = α ∙ Γ} 𝒳 f σ ς new = refl
f∘copair {Γ = α ∙ Γ} 𝒳 f σ ς (old v) = f∘copair 𝒳 f (σ ∘ old) ς v



-- module _ (𝒳ˢ : SubstitutionStructure 𝒳) where
--
--   open SubstitutionStructure 𝒳ˢ hiding (copair)
--
--   idm∘copair : (ρ : Γ ↝ Θ)(ϱ : Δ ↝ Θ)
--                (v : ℐ α (Γ ∔ Δ))
--              → copair 𝒳 (idm ∘ ρ) (idm ∘ ϱ) v ≡ idm (copair ℐ ρ ϱ v)
--   idm∘copair {∅} ρ ϱ v = refl
--   idm∘copair {α ∙ Γ} ρ ϱ new = refl
--   idm∘copair {α ∙ Γ} ρ ϱ (old v) = idm∘copair (ρ ∘ old) ϱ v
--   copair∘+₁ : {Γ₁ Γ₂ Δ₁ Δ₂ Θ : Ctx}{ρ : Γ₁ ↝ Γ₂}{ϱ : Δ₁ ↝ Δ₂}{σ : Γ₂ ~[ 𝒳 ]↝ Θ}{ς : Δ₂ ~[ 𝒳 ]↝ Θ}(v : ℐ α (Γ₁ ∔ Δ₁))
--             → copair 𝒳 σ ς ((ρ ∔.+₁ ϱ) v) ≡ copair 𝒳 (σ ∘ ρ) (ς ∘ ϱ) v
--   copair∘+₁ {Γ₁ = Γ₁}{Γ₂}{Δ₁}{Δ₂}{Θ}{ρ = ρ}{ϱ}{σ}{ς} v = begin
--         copair 𝒳 σ ς ((ρ ∔.+₁ ϱ) v)
--     ≡⟨⟩
--         copair 𝒳 σ ς (copair ℐ (∔.i₁ {Γ₂} ∘ ρ) (∔.i₂ {Γ₂} ∘ ϱ) v)
--     ≡⟨ f∘copair ℐ (copair 𝒳 σ ς) (∔.i₁ {Γ₂} ∘ ρ) (∔.i₂ {Γ₂} ∘ ϱ) v ⟩
--         copair 𝒳 (copair 𝒳 σ ς ∘ ∔.i₁ {Γ₂} ∘ ρ) (copair 𝒳 σ ς ∘ ∔.i₂ {Γ₂} ∘ ϱ) v
--     ≡⟨ 𝕊∔.[]-cong₂ 𝒳 𝒳ˢ (λ{ {v = v} → copair∘i₁ (ρ v) }) (λ{ {v = v} → copair∘i₂ {σ = σ} (ϱ v) }) {v = v} ⟩
--         copair 𝒳 (σ ∘ ρ) (ς ∘ ϱ) v
--     ∎ where open ≡-Reasoning


  --       copair 𝒳 σ ς ((ρ ∔.+₁ ϱ) v)
  --   ≡⟨⟩
  --       copair 𝒳 σ ς (copair ℐ (∔.i₁ {Γ₂} ∘ ρ) (∔.i₂ {Γ₂} ∘ ϱ) v)
  --   ≡⟨ f∘copair {Γ = {!   !}}{{!   !}}(copair 𝒳 σ ς) v ⟩
  --       copair 𝒳 (copair 𝒳 σ ς ∘ ∔.i₁ {Γ₂} ∘ ρ) (copair 𝒳 σ ς ∘ ∔.i₂ {Γ₂} ∘ ϱ) v
  --   ≡⟨ {!   !} ⟩
  --       copair 𝒳 (σ ∘ ρ) (ς ∘ ϱ) v
  --   ∎ where open ≡-Reasoning
