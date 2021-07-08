
-- Families with compatible monoid and coal
module SOAS.Coalgebraic.Monoid {T : Set} where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Variable
open import SOAS.Families.Core {T}
import SOAS.Families.Delta {T} as δ; open δ.Sorted
open import SOAS.Abstract.Hom {T}
import SOAS.Abstract.Box {T} as □ ; open □.Sorted
open import SOAS.Abstract.Monoid {T}
import SOAS.Abstract.Coalgebra {T} as →□ ; open →□.Sorted

open import SOAS.Coalgebraic.Map
open import SOAS.Coalgebraic.Strength
open import SOAS.Coalgebraic.Lift

private
  variable
    Γ Δ : Ctx
    α β : T

-- Coalgebraic monoid: family with compatible coalgebra and monoid structure
record CoalgMon (𝒳 : Familyₛ) : Set where
  field
    ᴮ : Coalgₚ 𝒳
    ᵐ : Mon 𝒳

  open Coalgₚ ᴮ public renaming (η to ηᴮ)
  open Mon ᵐ public hiding (ᵇ ; ᴮ ; r ; r∘η ; μᶜ) renaming (η to ηᵐ)

  field
    η-compat : {v : ℐ α Γ} → ηᴮ v ≡ ηᵐ v
    μ-compat : {ρ : Γ ↝ Δ}{t : 𝒳 α Γ} → r t ρ ≡ μ t (ηᵐ ∘ ρ)

  -- ᴮ : Coalgₚ 𝒳
  -- ᴮ = record { ᴮ = ᴮ ; η = η ; r∘η = trans compat lunit }

  open Coalgₚ ᴮ using (r∘η) public

  -- Multiplication of coalgebraic monoids is a pointed coalgebraic map
  μᶜ : Coalgebraic ᴮ ᴮ ᴮ μ
  μᶜ = record
    { r∘f = λ{ {σ = σ}{ϱ}{t} → begin
             r (μ t σ) ϱ                  ≡⟨ μ-compat ⟩
             μ (μ t σ) (ηᵐ ∘ ϱ)            ≡⟨ assoc ⟩
             μ t (λ v → μ (σ v) (ηᵐ ∘ ϱ))  ≡˘⟨ cong (μ t) (dext (λ _ → μ-compat)) ⟩
             μ t (λ v → r (σ v) ϱ)        ∎ }
    ; f∘r = λ{ {ρ = ρ}{ς}{t} → begin
             μ (r t ρ) ς                ≡⟨ cong (λ - → μ - ς) μ-compat ⟩
             μ (μ t (ηᵐ ∘ ρ)) ς          ≡⟨ assoc ⟩
             μ t (λ v → μ (ηᵐ (ρ v)) ς)  ≡⟨ cong (μ t) (dext (λ _ → lunit)) ⟩
             μ t (ς ∘ ρ)                ∎ }
    ; f∘η = trans (μ≈₂ η-compat) runit
    } where open ≡-Reasoning

  str-eq : (𝒴 : Familyₛ){F : Functor 𝔽amiliesₛ 𝔽amiliesₛ}(F:Str : Strength F)
           (open Functor F)(open Strength F:Str)
           (h : F₀ 〖 𝒳 , 𝒴 〗 α Γ)(σ : Γ ~[ 𝒳 ]↝ Δ)
         → str ᴮ 𝒴 h σ ≡ str (Mon.ᴮ ᵐ) 𝒴 h σ
  str-eq 𝒴 {F} F:Str h σ = begin
        str ᴮ 𝒴 h σ
    ≡⟨ str-nat₁ {f = id} (record { ᵇ⇒ = record { ⟨r⟩ = sym μ-compat }
                                               ; ⟨η⟩ = sym η-compat }) h σ ⟩
        str (Mon.ᴮ ᵐ) 𝒴 (F₁ id h) σ
    ≡⟨ congr identity (λ - → str (Mon.ᴮ ᵐ) 𝒴 - σ) ⟩
        str (Mon.ᴮ ᵐ) 𝒴 h σ
    ∎
    where
    open Functor F
    open Strength F:Str
    open ≡-Reasoning

  lift-eq : {Ξ : Ctx}(t : 𝒳 β (Ξ ∔ Γ))(σ : Γ ~[ 𝒳 ]↝ Δ) →
            μ t (lift ᴮ Ξ σ) ≡ μ t (lift (Mon.ᴮ ᵐ) Ξ σ)
  lift-eq {Ξ = Ξ} t σ = str-eq 𝒳 (δ:Strength Ξ) (μ t) σ
--
-- -- Coalgebraic monoid: family with compatible coalgebra and monoid structure
-- record CoalgMon (𝒳 : Familyₛ) : Set where
--   field
--     ᵇ : Coalg 𝒳
--     ᵐ : Mon 𝒳
--
--   open Coalg ᵇ public
--   open Mon ᵐ public hiding (ᵇ ; ᴮ ; r ; r∘η ; μᶜ)
--
--   field
--     compat : {ρ : Γ ↝ Δ}{t : 𝒳 α Γ} → r t ρ ≡ μ t (η ∘ ρ)
--
--   ᴮ : Coalgₚ 𝒳
--   ᴮ = record { ᵇ = ᵇ ; η = η ; r∘η = trans compat lunit }
--
--   open Coalgₚ ᴮ using (r∘η) public
--
--   -- Multiplication of coalgebraic monoids is a pointed coalgebraic map
--   μᶜ : Coalgebraic ᴮ ᴮ ᴮ μ
--   μᶜ = record
--     { r∘f = λ{ {σ = σ}{ϱ}{t} → begin
--              r (μ t σ) ϱ                  ≡⟨ compat ⟩
--              μ (μ t σ) (η ∘ ϱ)            ≡⟨ assoc ⟩
--              μ t (λ v → μ (σ v) (η ∘ ϱ))  ≡˘⟨ cong (μ t) (dext (λ _ → compat)) ⟩
--              μ t (λ v → r (σ v) ϱ)        ∎ }
--     ; f∘r = λ{ {ρ = ρ}{ς}{t} → begin
--              μ (r t ρ) ς                ≡⟨ cong (λ - → μ - ς) compat ⟩
--              μ (μ t (η ∘ ρ)) ς          ≡⟨ assoc ⟩
--              μ t (λ v → μ (η (ρ v)) ς)  ≡⟨ cong (μ t) (dext (λ _ → lunit)) ⟩
--              μ t (ς ∘ ρ)                ∎ }
--     ; f∘η = runit
--     } where open ≡-Reasoning
--
--   str-eq : (𝒴 : Familyₛ){F : Functor 𝔽amiliesₛ 𝔽amiliesₛ}(F:Str : Strength F)
--            (open Functor F)(open Strength F:Str)
--            (h : F₀ 〖 𝒳 , 𝒴 〗 α Γ)(σ : Γ ~[ 𝒳 ]↝ Δ)
--          → str ᴮ 𝒴 h σ ≡ str (Mon.ᴮ ᵐ) 𝒴 h σ
--   str-eq 𝒴 {F} F:Str h σ = begin
--         str ᴮ 𝒴 h σ
--     ≡⟨ str-nat₁ {f = id} (record { ᵇ⇒ = record { ⟨r⟩ = sym compat }
--                                  ; ⟨η⟩ = refl }) h σ ⟩
--         str (Mon.ᴮ ᵐ) 𝒴 (F₁ id h) σ
--     ≡⟨ congr identity (λ - → str (Mon.ᴮ ᵐ) 𝒴 - σ) ⟩
--         str (Mon.ᴮ ᵐ) 𝒴 h σ
--     ∎
--     where
--     open Functor F
--     open Strength F:Str
--     open ≡-Reasoning
--
--   lift-eq : {Ξ : Ctx}(t : 𝒳 β (Ξ ∔ Γ))(σ : Γ ~[ 𝒳 ]↝ Δ) →
--             μ t (lift ᴮ Ξ σ) ≡ μ t (lift (Mon.ᴮ ᵐ) Ξ σ)
--   lift-eq {Ξ = Ξ} t σ = str-eq 𝒳 (δ:Strength Ξ) (μ t) σ
