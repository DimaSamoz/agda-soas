

import SOAS.Families.Core

-- Combinators for context maps
module SOAS.ContextMaps.Combinators {T : Set}
  (open SOAS.Families.Core {T})
  (𝒳 : Familyₛ) where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Sorting
open import SOAS.Variable
open import SOAS.Families.Isomorphism
open import SOAS.Families.BCCC

private
  variable
    Γ Γ′ Δ Δ′ Θ : Ctx
    α β τ : T


-- Sub from the empty context
empty : ∅ ~[ 𝒳 ]↝ Δ
empty ()

-- Combine two maps into the same context by concatenating the domain
copair : Γ ~[ 𝒳 ]↝ Θ → Δ ~[ 𝒳 ]↝ Θ → (Γ ∔ Δ) ~[ 𝒳 ]↝ Θ
copair {∅} σ ς v = ς v
copair {α ∙ Γ} σ ς new = σ new
copair {α ∙ Γ} σ ς (old v) = copair {Γ} (σ ∘ old) ς v

copair≈₁ : {σ₁ σ₂ : Γ ~[ 𝒳 ]↝ Θ}(ς : Δ ~[ 𝒳 ]↝ Θ){v : ℐ α (Γ ∔ Δ)}
         → ({τ : T}(v : ℐ τ Γ) → σ₁ v ≡ σ₂ v)
         → copair σ₁ ς v ≡ copair σ₂ ς v
copair≈₁ ς {v} p = cong (λ - → copair (λ {τ} → - {τ}) ς v) (dext (λ y → p y))
copair≈₂ : (σ : Γ ~[ 𝒳 ]↝ Θ){ς₁ ς₂ : Δ ~[ 𝒳 ]↝ Θ}{v : ℐ α (Γ ∔ Δ)}
         → ({τ : T}(v : ℐ τ Δ) → ς₁ v ≡ ς₂ v)
         → copair σ ς₁ v ≡ copair σ ς₂ v
copair≈₂ σ {v = v} p = cong (λ - → copair σ (λ {τ} → - {τ}) v) (dext (λ y → p y))

-- Split a map from a combined context into two maps
split : (Γ ∔ Δ) ~[ 𝒳 ]↝ Θ → Γ ~[ 𝒳 ]↝ Θ × Δ ~[ 𝒳 ]↝ Θ
split {∅} σ = (λ ()) , σ
split {α ∙ Γ} σ with split {Γ} (σ ∘ old)
... | ς₁ , ς₂ = (λ{ new → σ new ; (old v) → ς₁ v}) , ς₂

-- Expand the codomain of a renaming
expandʳ : ({Γ} Δ : Ctx) → Γ ↝ Γ ∔ Δ
expandʳ {α ∙ Γ} Δ new = new
expandʳ {α ∙ Γ} Δ (old v) = old (expandʳ Δ v)

expandˡ : (Γ {Δ} : Ctx) → Δ ↝ Γ ∔ Δ
expandˡ ∅ v = v
expandˡ (α ∙ Γ) v = old (expandˡ Γ v)


-- Special cases of the above, when one of the contexts is a singleton
-- and the map from the singleton context is isomorphic to a term

-- Add a term to a context map
add : 𝒳 α Δ → Γ ~[ 𝒳 ]↝ Δ → (α ∙ Γ) ~[ 𝒳 ]↝ Δ
add t σ new = t
add t σ (old v) = σ v

-- Consider a term as a context map from the singleton context
asMap : 𝒳 α Γ → ⌊ α ⌋ ~[ 𝒳 ]↝ Γ
asMap t new = t

-- Separate a compound context map into a term and a residual map
detach : (τ ∙ Γ) ~[ 𝒳 ]↝ Δ → 𝒳 τ Δ × (Γ ~[ 𝒳 ]↝ Δ)
detach {_}{∅} σ = σ new , (λ ())
detach {_}{(α ∙ Γ)} σ = σ new , σ ∘ old

add[new][old] : (σ : τ ∙ Γ ~[ 𝒳 ]↝ Δ)(v : ℐ α (τ ∙ Γ))
             → add (σ new) (σ ∘ old) v ≡ σ v
add[new][old] σ new = refl
add[new][old] σ (old v) = refl

-- Remove a term from a compound context map
remove : (τ ∙ Γ) ~[ 𝒳 ]↝ Δ → Γ ~[ 𝒳 ]↝ Δ
remove {_} {∅} σ = λ ()
remove {_} {α ∙ Γ} σ = σ ∘ old

-- Add and remove are inverses
add∘remove : (σ : (τ ∙ Γ) ~[ 𝒳 ]↝ Δ) (v : ℐ α (τ ∙ Γ))
           → add (σ new) (remove σ) v
           ≡ σ v
add∘remove σ new = refl
add∘remove σ (old new) = refl
add∘remove σ (old (old v)) = refl

remove∘add : (σ : Γ ~[ 𝒳 ]↝ Δ) (t : 𝒳 τ Δ)(v : ℐ α Γ)
           → remove (add t σ) v
           ≡ σ v
remove∘add σ t new = refl
remove∘add σ t (old v) = refl
