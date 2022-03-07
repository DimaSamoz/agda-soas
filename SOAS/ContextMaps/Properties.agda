

-- Various properties of context map operations
module SOAS.ContextMaps.Properties {T : Set} where

open import SOAS.Families.Core
open import SOAS.Families.Discrete

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


module _ (𝒳 : Familyₛ) where
  -- Copairing and injection
  copair∘inl : {σ : Γ ~[ 𝒳 ]↝ Θ}{ς : Δ ~[ 𝒳 ]↝ Θ} (v : ℐ α Γ)
            → copair 𝒳 σ ς (∔.i₁ v) ≡ σ v
  copair∘inl new = refl
  copair∘inl {σ = σ} (old v) = copair∘inl {σ = σ ∘ old} v

  copair∘inr : {σ : Γ ~[ 𝒳 ]↝ Θ}{ς : Δ ~[ 𝒳 ]↝ Θ} (v : ℐ α Δ)
            → copair 𝒳 σ ς (∔.i₂  {Γ} v) ≡ ς v
  copair∘inr {Γ = ∅} v = refl
  copair∘inr {Γ = α ∙ Γ} {σ = σ} v = copair∘inr {σ = σ ∘ old} v


  -- Push function into copairing
  f∘copair : ({𝒴} : Familyₛ) (f : Θ ~[ 𝒳 ➔ 𝒴 ]↝ Ξ)(σ : Γ ~[ 𝒳 ]↝ Θ)(ς : Δ ~[ 𝒳 ]↝ Θ)
            (v : ℐ α (Γ ∔ Δ))
           → f (copair 𝒳 σ ς v) ≡ copair 𝒴 (f ∘ σ) (f ∘ ς) v
  f∘copair {Γ = ∅} f σ ς v = refl
  f∘copair {Γ = α ∙ Γ} f σ ς new = refl
  f∘copair {Γ = α ∙ Γ} f σ ς (old v) = f∘copair f (σ ∘ old) ς v

-- η-contraction for copairing
copair-η : (Γ Δ : Ctx)(v : ℐ α (Γ ∔ Δ)) → copair ℐ (inl Γ) (inr Γ) v ≡ v
copair-η Γ Δ v = ∔.+-η {Γ}{Δ}{v = v}

-- Cocartesian associativity with empty first context
↝assocʳ∅ : (Δ Θ : Ctx){α : T}(v : ℐ α (Δ ∔ Θ)) → ↝assocʳ ∅ Δ Θ v ≡ v
↝assocʳ∅ Δ Θ v = ∔.+-η {Δ}{Θ}

↝assocˡ∅ : (Δ Θ : Ctx){α : T}(v : ℐ α (Δ ∔ Θ)) → ↝assocˡ ∅ Δ Θ v ≡ v
↝assocˡ∅ Δ Θ v = ∔.+-η {Δ}{Θ}

-- Cocartesian associativity with compound first context
↝assocˡ∙ : (Γ Δ Θ : Ctx){τ α : T}(v : ℐ α (Γ ∔ (Δ ∔ Θ)))
       → ↝assocˡ (τ ∙ Γ) Δ Θ (old v) ≡ old (↝assocˡ Γ Δ Θ v)
↝assocˡ∙ Γ Δ Θ {τ} v = begin
      ↝assocˡ (τ ∙ Γ) Δ Θ (old v)
  ≡⟨⟩
      copair ℐ (old ∘ inl (Γ ∔ Δ) ∘ inl Γ) (copair ℐ (old ∘ inl (Γ ∔ Δ) ∘ inr Γ) (old ∘ inr (Γ ∔ Δ))) v
  ≡˘⟨ copair≈₂ ℐ (old ∘ inl (Γ ∔ Δ) ∘ inl Γ) (f∘copair ℐ old (inl (Γ ∔ Δ) ∘ inr Γ) (inr (Γ ∔ Δ))) ⟩
      copair ℐ (old ∘ inl (Γ ∔ Δ) ∘ inl Γ) (old ∘ copair ℐ (inl (Γ ∔ Δ) ∘ inr Γ) (inr (Γ ∔ Δ))) v
  ≡˘⟨ f∘copair ℐ old (inl (Γ ∔ Δ) ∘ inl Γ) (copair ℐ (inl (Γ ∔ Δ) ∘ inr Γ) (inr (Γ ∔ Δ))) v ⟩
      old (↝assocˡ Γ Δ Θ v)
  ∎ where open ≡-Reasoning

↝assocʳ∙ : (Γ Δ Θ : Ctx){τ α : T}(v : ℐ α ((Γ ∔ Δ) ∔ Θ))
       → ↝assocʳ (τ ∙ Γ) Δ Θ (old v) ≡ old (↝assocʳ Γ Δ Θ v)
↝assocʳ∙ Γ Δ Θ {τ} v =
  begin
      ↝assocʳ (τ ∙ Γ) Δ Θ (old v)
  ≡⟨⟩
      copair ℐ (copair ℐ (inl (τ ∙ Γ)) (inr (τ ∙ Γ) ∘ inl Δ)) (inr (τ ∙ Γ) ∘ inr Δ) (old v)
  ≡⟨⟩
      copair ℐ (copair ℐ (old ∘ inl Γ) (old ∘ inr Γ ∘ inl Δ)) (old ∘ inr Γ ∘ inr Δ) v
  ≡˘⟨ copair≈₁ ℐ (old ∘ inr Γ ∘ inr Δ) (f∘copair ℐ old (inl Γ) (inr Γ ∘ inl Δ)) ⟩
      copair ℐ (old ∘ copair ℐ (inl Γ) (inr Γ ∘ inl Δ)) (old ∘ inr Γ ∘ inr Δ) v
  ≡˘⟨ f∘copair ℐ old (copair ℐ (inl Γ) (inr Γ ∘ inl Δ)) (inr Γ ∘ inr Δ) v ⟩
      old (copair ℐ (copair ℐ (inl Γ) (inr Γ ∘ inl Δ)) (inr Γ ∘ inr Δ) v)
  ≡⟨⟩
      old (↝assocʳ Γ Δ Θ v)
  ∎ where open ≡-Reasoning



-- Discrete associator on variables
assocˡ-new : (Γ Δ Θ : Ctx){τ : T}
       → assocˡ ℐ (τ ∙ Γ) Δ Θ new ≡ new
assocˡ-new ∅ Δ Θ = refl
assocˡ-new (α ∙ Γ) Δ Θ rewrite ∔-assoc Γ Δ Θ = refl

assocˡ-old : (Γ Δ Θ : Ctx){τ α : T}(v : ℐ α (Γ ∔ (Δ ∔ Θ)))
       → assocˡ ℐ (τ ∙ Γ) Δ Θ (old v) ≡ old (assocˡ ℐ Γ Δ Θ v)
assocˡ-old ∅ Δ Θ v = refl
assocˡ-old (α ∙ Γ) Δ Θ v rewrite ∔-assoc Γ Δ Θ = refl

module _ (𝒳 : Familyₛ) where
  -- Cocartesian associator and copairing
  copair∘↝assocˡ : (f : Γ ~[ 𝒳 ]↝ Ξ)(g : Δ ~[ 𝒳 ]↝ Ξ)(h : Θ ~[ 𝒳 ]↝ Ξ)(v : ℐ α (Γ ∔ (Δ ∔ Θ)))
                → copair 𝒳 (copair 𝒳 f g) h (↝assocˡ Γ Δ Θ v) ≡ copair 𝒳 f (copair 𝒳 g h) v
  copair∘↝assocˡ {∅}{Δ = Δ}{Θ = Θ} f g h v = cong (copair 𝒳 g h) (↝assocˡ∅ Δ Θ v)
  copair∘↝assocˡ {α ∙ Γ} f g h new = refl
  copair∘↝assocˡ {α ∙ Γ}{Δ = Δ}{Θ = Θ} f g h (old v) = begin
        copair 𝒳 (copair 𝒳 f g) h (↝assocˡ (α ∙ Γ) Δ Θ (old v))
    ≡⟨ cong (copair 𝒳 (copair 𝒳 f g) h) (↝assocˡ∙ Γ Δ Θ v) ⟩
        copair 𝒳 (copair 𝒳 f g) h (old (↝assocˡ Γ Δ Θ v))
    ≡⟨ copair∘↝assocˡ (f ∘ old) g h v ⟩
        copair 𝒳 f (copair 𝒳 g h) (old v)
    ∎ where open ≡-Reasoning


  copair∘assocˡ : (f : Γ ~[ 𝒳 ]↝ Ξ)(g : Δ ~[ 𝒳 ]↝ Ξ)(h : Θ ~[ 𝒳 ]↝ Ξ)(v : ℐ α (Γ ∔ (Δ ∔ Θ)))
                → copair 𝒳 (copair 𝒳 f g) h (assocˡ ℐ Γ Δ Θ v) ≡ copair 𝒳 f (copair 𝒳 g h) v
  copair∘assocˡ {Γ = ∅} {Δ = Δ} {Θ = Θ} f g h v = refl
  copair∘assocˡ {Γ = α ∙ Γ} {Δ = Δ} {Θ = Θ} f g h new = cong (copair 𝒳 (copair 𝒳 f g) h) (assocˡ-new Γ Δ Θ)
  copair∘assocˡ {Γ = α ∙ Γ} {Δ = Δ} {Θ = Θ} f g h (old v) = begin
        copair 𝒳 (copair 𝒳 f g) h (assocˡ ℐ (α ∙ Γ) Δ Θ (old v))
    ≡⟨ cong (copair 𝒳 (copair 𝒳 f g) h) (assocˡ-old Γ Δ Θ v) ⟩
        copair 𝒳 (copair 𝒳 f g) h (old (assocˡ ℐ Γ Δ Θ v))
    ≡⟨ copair∘assocˡ (f ∘ old) g h v ⟩
        copair 𝒳 (f ∘ old) (copair 𝒳 g h) v
    ∎ where open ≡-Reasoning

-- Cocartesian associator matches discrete associator on variables
assocˡ≈↝assocˡ : (Γ {Δ Θ} : Ctx)(v : ℐ α (Γ ∔ (Δ ∔ Θ)))
               → assocˡ ℐ Γ Δ Θ (v) ≡ ↝assocˡ Γ Δ Θ v
assocˡ≈↝assocˡ ∅ {Δ} {Θ} v = sym (copair-η Δ Θ v)
assocˡ≈↝assocˡ (α ∙ Γ) {Δ} {Θ} new = assocˡ-new Γ Δ Θ
assocˡ≈↝assocˡ (α ∙ Γ) {Δ} {Θ} (old v) = begin
      assocˡ ℐ (α ∙ Γ) Δ Θ (old v)
  ≡⟨ assocˡ-old Γ Δ Θ v ⟩
      old (assocˡ ℐ Γ Δ Θ v)
  ≡⟨ cong old (assocˡ≈↝assocˡ Γ v) ⟩
      old (↝assocˡ Γ Δ Θ v)
  ≡˘⟨ ↝assocˡ∙ Γ Δ Θ v ⟩
      ↝assocˡ (α ∙ Γ) Δ Θ (old v)
  ∎ where open ≡-Reasoning
