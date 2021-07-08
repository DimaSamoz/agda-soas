
-- Closed monoid in the skew-closed category of families
module SOAS.Abstract.Monoid {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.ContextMaps.Combinators

open import SOAS.Construction.Structure as Structure

open import SOAS.Abstract.Hom {T}
open import SOAS.Abstract.Coalgebra using (module Sorted) ; open Sorted
open import SOAS.Families.Core {T}

open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import SOAS.Coalgebraic.Map {T}
open import SOAS.Coalgebraic.Lift {T}

private
  variable
    Γ Δ Θ : Ctx
    α β γ : T

record Mon (𝒳 : Familyₛ) : Set where
  field
    η : ℐ ⇾̣ 𝒳
    μ : 𝒳 ⇾̣ 〖 𝒳 , 𝒳 〗

    lunit : {σ : Γ ~[ 𝒳 ]↝ Δ}{v : ℐ α Γ}
          → μ (η v) σ ≡ σ v
    runit : {t : 𝒳 α Γ} → μ t η ≡ t
    assoc : {σ : Γ ~[ 𝒳 ]↝ Δ}{ς : Δ ~[ 𝒳 ]↝ Θ} {t : 𝒳 α Γ}
          → μ (μ t σ) ς ≡ μ t (λ v → μ (σ v) ς)

  -- Congruence in both arguments of the multiplication
  μ≈₁ : {t₁ t₂ : 𝒳 α Γ}{σ : Γ ~[ 𝒳 ]↝ Δ}
      → t₁ ≡ t₂
      → μ t₁ σ ≡ μ t₂ σ
  μ≈₁ refl = refl

  μ≈₂ : {t : 𝒳 α Γ}{σ ς : Γ ~[ 𝒳 ]↝ Δ}
      → ({τ : T}{v : ℐ τ Γ} → σ v ≡ ς v)
      → μ t σ ≡ μ t ς
  μ≈₂ {t = t} p = cong (μ t) (dext′ p)

  -- Monoids are pointed coalgebras
  ᵇ : Coalg 𝒳
  ᵇ = record { r = λ t ρ →  μ t (η ∘ ρ) ; counit = runit
    ; comult = λ { {t = t} → sym (trans assoc (μ≈₂ lunit)) } }

  ᴮ : Coalgₚ 𝒳
  ᴮ = record { ᵇ = ᵇ ; η = η ; r∘η = lunit }

  -- Single-variable substitution
  [_/] : 𝒳 α Γ → 𝒳 β (α ∙ Γ) → 𝒳 β Γ
  [ s /] t = μ t (add 𝒳 s η)

  -- Substitution for second variable
  [_/]′ : 𝒳 α Γ → 𝒳 γ (β ∙ α ∙ Γ) → 𝒳 γ (β ∙ Γ)
  [ s /]′ t = μ t (lift₁ ᴮ (add 𝒳 s η))

  -- Substitution for top two variables
  [_,_/]₂ : 𝒳 α Γ → 𝒳 β Γ → 𝒳 γ (α ∙ β ∙ Γ) → 𝒳 γ Γ
  [ s₁ , s₂ /]₂ t = μ t (add 𝒳 s₁ (add 𝒳 s₂ η))


  open Coalgₚ ᴮ public using (r ; r∘η)

  -- Multiplication is coalgebraic map
  μᶜ : Coalgebraic ᴮ ᴮ ᴮ μ
  μᶜ = record { r∘f = assoc ; f∘r = trans assoc (μ≈₂ lunit) ; f∘η = lunit }


-- Monoid homomorphisms
record Mon⇒ {𝒳 𝒴 : Familyₛ}(𝒳ᵐ : Mon 𝒳)(𝒴ᵐ : Mon 𝒴)
               (f : 𝒳 ⇾̣ 𝒴) : Set where

  private module 𝒳 = Mon 𝒳ᵐ
  private module 𝒴 = Mon 𝒴ᵐ

  field
    ⟨η⟩ : {v : ℐ α Γ} → f (𝒳.η v) ≡ 𝒴.η v
    ⟨μ⟩ : {σ : Γ ~[ 𝒳 ]↝ Δ}{t : 𝒳 α Γ}
        → f (𝒳.μ t σ) ≡ 𝒴.μ (f t) (f ∘ σ)

  ᵇ⇒ : Coalg⇒ 𝒳.ᵇ 𝒴.ᵇ f
  ᵇ⇒ = record { ⟨r⟩ = trans ⟨μ⟩ (𝒴.μ≈₂ ⟨η⟩) }

  ᴮ⇒ : Coalgₚ⇒ 𝒳.ᴮ 𝒴.ᴮ f
  ᴮ⇒ = record { ᵇ⇒ = ᵇ⇒ ; ⟨η⟩ = ⟨η⟩ }

  -- Preservation of multiplication and unit implies the semantic substitution
  -- lemma for single- and double-variable substitution
  sub-lemma : (s : 𝒳 α Γ)(t : 𝒳 β (α ∙ Γ)) →
              f (𝒳.[ s /] t) ≡ 𝒴.[ f s /] (f t)
  sub-lemma s t = trans ⟨μ⟩ (cong (𝒴.μ (f t))
                        (dext λ{ new → refl ; (old y) → ⟨η⟩}))

  sub-lemma₂ : (s₁ : 𝒳 α Γ)(s₂ : 𝒳 β Γ)(t : 𝒳 γ (α ∙ β ∙ Γ)) →
               f (𝒳.[ s₁ , s₂ /]₂ t) ≡ 𝒴.[ f s₁ , f s₂ /]₂ (f t)
  sub-lemma₂ s₁ s₂ t = trans ⟨μ⟩ (cong (𝒴.μ (f t))
                             (dext λ{ new → refl ; (old new) → refl
                                    ; (old (old y)) → ⟨η⟩}))


module MonoidStructure = Structure 𝔽amiliesₛ Mon

-- Category of substitution monoids
𝕄onoids : Category 1ℓ 0ℓ 0ℓ
𝕄onoids = MonoidStructure.StructCat record
  { IsHomomorphism = Mon⇒
  ; id-hom = record { ⟨η⟩ = refl ; ⟨μ⟩ = refl }
  ; comp-hom = λ g f gᵐ⇒ fᵐ⇒ → record
    { ⟨η⟩ = trans (cong g (⟨η⟩ fᵐ⇒)) (⟨η⟩ gᵐ⇒)
    ; ⟨μ⟩ = trans (cong g (⟨μ⟩ fᵐ⇒)) (⟨μ⟩ gᵐ⇒)
    }
  } where open Mon⇒

module 𝕄on = Category 𝕄onoids

Monoid : Set₁
Monoid = 𝕄on.Obj

Monoid⇒ : Monoid → Monoid → Set
Monoid⇒ = 𝕄on._⇒_

module AsMonoid (ℳᵐ : Monoid) where
  open Object ℳᵐ renaming (𝐶 to ℳ; ˢ to ᵐ) public
  open Mon ᵐ public



module AsMonoid⇒ {ℳᵐ 𝒩ᵐ : Monoid} (fᵐ⇒ : Monoid⇒ ℳᵐ 𝒩ᵐ) where
  open Morphism fᵐ⇒ renaming (𝑓 to f ; ˢ⇒ to ᵐ⇒) public
  open Mon⇒ ᵐ⇒ public
