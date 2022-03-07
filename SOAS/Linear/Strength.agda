
-- Linear closed strength
module SOAS.Linear.Strength {T : Set} where

open import SOAS.Families.Core {T}
open import SOAS.Context
open import SOAS.Variable
open import SOAS.ContextMaps.Combinators
open import SOAS.ContextMaps.CategoryOfRenamings

open import SOAS.Common
open import SOAS.Coalgebraic.Map
open import SOAS.Coalgebraic.Strength
import SOAS.Abstract.Coalgebra as →□ ; open →□.Sorted
open import SOAS.Abstract.Hom

open import SOAS.Linear.Exponential
open import SOAS.Linear.Tensor
open import SOAS.Linear.Distributor

private
  variable
    X Y : Family
    𝒳 𝒴 𝒵 𝒫 𝒬 : Familyₛ
    Γ Δ Θ : Ctx
    α : T

-- Exponential strength of an endofunctor
record LinStrength (Fᶠ : Functor 𝔽amiliesₛ 𝔽amiliesₛ) : Set₁ where
  open Functor Fᶠ

  field
    -- Strength transformation that lifts a 𝒴-substitution over an endofunctor F₀
    lstr : (𝒴 : Familyₛ) → F₀ (X ⊸ 𝒴) ⇾̣ (X ⊸ F₀ 𝒴)

    -- Naturality
    lstr-nat₁ : (f : Y ⇾ X)(e : F₀ (X ⊸ 𝒵) α Γ)(y : Y Δ)
        → lstr 𝒵 e (f y)
        ≡ lstr 𝒵 (F₁ {X ⊸ 𝒵}{Y ⊸ 𝒵}(_∘ f) e) y

    lstr-nat₂ : (g : 𝒴 ⇾̣ 𝒵)(e : F₀ (X ⊸ 𝒴) α Γ)(x : X Δ)
      → lstr 𝒵 (F₁ {X ⊸ 𝒴}{X ⊸ 𝒵} (g ∘_) e) x
      ≡ F₁ g (lstr 𝒴 e x)

    -- Compatibility with currying
    lstr-curry : (t : F₀ ((X ⊗ Y) ⊸ 𝒵) α Γ)(x : X Δ)(y : Y Θ)
             → curry° (F₀ 𝒵) (lstr 𝒵 t) x y
             ≡ lstr 𝒵 (lstr (Y ⊸ 𝒵) (F₁ (curry° 𝒵) t) x) y

  lstr≈₁ : {t₁ t₂ : F₀ (X ⊸ 𝒴) α Γ}{x : X Δ}
         → (t₁ ≡ t₂)
         → lstr 𝒴 t₁ x ≡ lstr 𝒴 t₂ x
  lstr≈₁ refl = refl

-- Compatible coalgebraic and linear strengths
record CompatStrengths (Fᶠ : Functor 𝔽amiliesₛ 𝔽amiliesₛ) : Set₁ where
  open Functor Fᶠ
  field
    CoalgStr : Strength Fᶠ
    LinStr : LinStrength Fᶠ

  open Strength CoalgStr public
  open LinStrength LinStr public

  field
    -- https://tinyurl.com/yd67adkh
    compat-strs : {X : Family}(𝒫ᴮ : Coalgₚ 𝒫)
            (t : F₀ (X ⊸ 〖 𝒫 , 𝒴 〗) α Γ)(σ : Γ ~[ X ⊸ 𝒫 ]↝ Δ)(x : X Θ)
            (open Coalgₚ 𝒫ᴮ)
            → dist X η (F₀ 𝒴) (λ x → str 𝒫ᴮ 𝒴 (lstr 〖 𝒫 , 𝒴 〗 t x)) σ x
            ≡ lstr 𝒴 (str (X ⊸ᴮ 𝒫ᴮ) (X ⊸ 𝒴) (F₁ (λ{ l σ → dist X η 𝒴 l σ}) t) σ) x
