
-- Coalgebraic strength over an endofunctor
module SOAS.Coalgebraic.Strength {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core {T}
open import SOAS.Abstract.Hom {T}
import SOAS.Abstract.Box {T} as □ ; open □.Sorted
import SOAS.Abstract.Coalgebra {T} as →□ ; open →□.Sorted

open import SOAS.Coalgebraic.Map


private
  variable
    Γ Δ Θ : Ctx
    α : T

-- Pointed coalgebraic strength for a family endofunctor
record Strength (Fᶠ : Functor 𝔽amiliesₛ 𝔽amiliesₛ) : Set₁ where
  open Functor Fᶠ
  open Coalg

  field
    -- Strength transformation that lifts a 𝒫-substitution over an endofunctor F₀
    str : {𝒫 : Familyₛ}(𝒫ᴮ : Coalgₚ 𝒫)(𝒳 : Familyₛ)
        → F₀ 〖 𝒫 , 𝒳 〗 ⇾̣ 〖 𝒫 , F₀ 𝒳 〗

    -- Naturality conditions for the two components
    str-nat₁ : {𝒫 𝒬 𝒳 : Familyₛ}{𝒫ᴮ : Coalgₚ 𝒫}{𝒬ᴮ : Coalgₚ 𝒬}
             → {f : 𝒬 ⇾̣ 𝒫} (fᴮ⇒ : Coalgₚ⇒ 𝒬ᴮ 𝒫ᴮ f)
             → (h : F₀ 〖 𝒫 , 𝒳 〗 α Γ) (σ : Γ ~[ 𝒬 ]↝ Δ)
      → str 𝒫ᴮ 𝒳 h (f ∘ σ)
      ≡ str 𝒬ᴮ 𝒳 (F₁ (λ{ h′ ς → h′ (λ v → f (ς v))}) h) σ

    str-nat₂ : {𝒫 𝒳 𝒴 : Familyₛ}{𝒫ᴮ : Coalgₚ 𝒫}
             → (f : 𝒳 ⇾̣ 𝒴)(h : F₀ 〖 𝒫 , 𝒳 〗 α Γ)(σ : Γ ~[ 𝒫 ]↝ Δ)
      → str 𝒫ᴮ 𝒴 (F₁ (λ{ h′ ς → f (h′ ς)}) h) σ
      ≡ F₁ f (str 𝒫ᴮ 𝒳 h σ)

    -- Unit law
    str-unit : (𝒳 : Familyₛ)(h : F₀ 〖 ℐ , 𝒳 〗 α Γ)
      → str ℐᴮ 𝒳 h id
      ≡ F₁ (i 𝒳) h

    -- Associativity law for a particular pointed coalgebraic map f
    str-assoc  : (𝒳 : Familyₛ){𝒫 𝒬 ℛ : Familyₛ}
                 {𝒫ᴮ : Coalgₚ 𝒫} {𝒬ᴮ : Coalgₚ 𝒬} {ℛᴮ : Coalgₚ ℛ}
                 {f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗}
                 (fᶜ : Coalgebraic 𝒫ᴮ 𝒬ᴮ ℛᴮ f) (open Coalgebraic fᶜ)
                 (h : F₀ 〖 ℛ , 𝒳 〗 α Γ)(σ : Γ ~[ 𝒫 ]↝ Δ)(ς : Δ ~[ 𝒬 ]↝ Θ)
      → str ℛᴮ 𝒳 h (λ v → f (σ v) ς)
      ≡ str 𝒬ᴮ 𝒳 (str 〖𝒫,𝒴〗ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (L 𝒬 ℛ 𝒳) h) (f ∘ σ)) ς

  str≈₁ : {𝒫 : Familyₛ}{𝒫ᴮ : Coalgₚ 𝒫}{𝒳 : Familyₛ}
        → {t₁ t₂ : F₀ 〖 𝒫 , 𝒳 〗 α Γ}{σ : Γ ~[ 𝒫 ]↝ Δ}
        → t₁ ≡ t₂
        → str 𝒫ᴮ 𝒳 t₁ σ ≡ str 𝒫ᴮ 𝒳 t₂ σ
  str≈₁ refl = refl

  module _ (𝒳 {𝒫 𝒬 ℛ} : Familyₛ) where

    -- Precompose an internal hom by a parametrised map
    precomp : (f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗) → 〖 ℛ , 𝒳 〗 ⇾̣ 〖 𝒫 , 〖 𝒬 , 𝒳 〗 〗
    precomp f h σ ς = h (λ v → f (σ v) ς)

    -- Corollary: strength distributes over pointed coalgebraic maps
    str-dist : {𝒫ᴮ : Coalgₚ 𝒫} {𝒬ᴮ : Coalgₚ 𝒬} {ℛᴮ : Coalgₚ ℛ}
               {f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗}
               (fᶜ : Coalgebraic 𝒫ᴮ 𝒬ᴮ ℛᴮ f)
               (h : F₀ 〖 ℛ , 𝒳 〗 α Γ)(σ : Γ ~[ 𝒫 ]↝ Δ)(ς : Δ ~[ 𝒬 ]↝ Θ)
      → str ℛᴮ 𝒳 h (λ v → f (σ v) ς)
      ≡ str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (precomp f) h) σ) ς
    str-dist {𝒫ᴮ = 𝒫ᴮ} {𝒬ᴮ} {ℛᴮ} {f} fᶜ h σ ς =
      begin
          str ℛᴮ 𝒳 h (λ v → f (σ v) ς)
      ≡⟨ str-assoc 𝒳 fᶜ h σ ς ⟩
          str 𝒬ᴮ 𝒳 (str 〖𝒫,𝒴〗ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (L 𝒬 ℛ 𝒳) h) (f ∘ σ)) ς
      ≡⟨ cong (λ - → str 𝒬ᴮ 𝒳 - ς) (str-nat₁ fᴮ⇒ (F₁ (L 𝒬 ℛ 𝒳) h) σ) ⟩
          str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 (F₁ 〖 f , 〖 𝒬 , 𝒳 〗 〗ₗ
                                        (F₁ (L 𝒬 ℛ 𝒳) h)) σ) ς
      ≡˘⟨ cong (λ - → str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 - σ) ς) homomorphism ⟩
          str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (precomp f) h) σ) ς
      ∎
      where
      open ≡-Reasoning
      open Coalgebraic fᶜ renaming (ᴮ⇒ to fᴮ⇒)

  -- Target of a strong functor is a coalgebra
  Fᵇ : {𝒫 : Familyₛ}(𝒫ᵇ : Coalg 𝒫) → Coalg (F₀ 𝒫)
  Fᵇ {𝒫} 𝒫ᵇ = record
    { r = str ℐᴮ 𝒫 ∘ F₁ (r 𝒫ᵇ)
    ; counit = λ{ {t = t} → begin
          str ℐᴮ 𝒫 (F₁ (r 𝒫ᵇ) t) id
      ≡⟨ str-unit 𝒫 (F₁ (r 𝒫ᵇ) t) ⟩
          F₁ (i 𝒫) (F₁ (r 𝒫ᵇ) t)
      ≡˘⟨ homomorphism ⟩
          F₁ (λ t → r 𝒫ᵇ t id) t
      ≡⟨ F-resp-≈ (counit 𝒫ᵇ) ⟩
          F₁ id t
      ≡⟨ identity ⟩
          t
      ∎ }
    ; comult = λ{ {ρ = ρ}{ϱ}{t} → begin
          str ℐᴮ 𝒫 (F₁ (r 𝒫ᵇ) t) (ϱ ∘ ρ)
      ≡⟨ str-dist 𝒫 (jᶜ ℐᴮ) (F₁ (r 𝒫ᵇ) t) ρ ϱ ⟩
          str ℐᴮ 𝒫 (str ℐᴮ (□ 𝒫) (F₁ (λ{ b ρ ϱ → b (ϱ ∘ ρ)}) (F₁ (r 𝒫ᵇ) t)) ρ) ϱ
      ≡˘⟨ str≈₁ (str≈₁ homomorphism) ⟩
          str ℐᴮ 𝒫 (str ℐᴮ (□ 𝒫) (F₁ (λ{ t ρ ϱ → r 𝒫ᵇ t (ϱ ∘ ρ) }) t) ρ) ϱ
      ≡⟨ str≈₁ (str≈₁ (F-resp-≈ (dext² (λ ρ ϱ → comult 𝒫ᵇ)))) ⟩
          str ℐᴮ 𝒫 (str ℐᴮ (□ 𝒫) (F₁ (λ{ t ρ ϱ → r 𝒫ᵇ (r 𝒫ᵇ t ρ) ϱ }) t) ρ) ϱ
      ≡⟨ str≈₁ (str≈₁ homomorphism) ⟩
          str ℐᴮ 𝒫 (str ℐᴮ (□ 𝒫) (F₁ {□ 𝒫}{□ (□ 𝒫)}(r 𝒫ᵇ ∘_) (F₁ (r 𝒫ᵇ) t)) ρ) ϱ
      ≡⟨ str≈₁ (str-nat₂ (r 𝒫ᵇ) (F₁ (r 𝒫ᵇ) t) ρ) ⟩
          str ℐᴮ 𝒫 (F₁ (r 𝒫ᵇ) (str ℐᴮ 𝒫 (F₁ (r 𝒫ᵇ) t) ρ)) ϱ
      ∎ }
    } where open ≡-Reasoning
