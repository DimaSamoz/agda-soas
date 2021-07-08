
-- Parametrised maps of families and their coalgebraic properties
module SOAS.Coalgebraic.Map {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core {T}
open import SOAS.Abstract.Hom {T}
import SOAS.Abstract.Box {T} as □ ;  open □.Sorted
import SOAS.Abstract.Coalgebra {T} as →□ ; open →□.Sorted

private
  variable
    𝒳 𝒴 𝒫 : Familyₛ
    Γ Δ Θ : Ctx
    α : T

record Coalgebraic (𝒳ᴮ : Coalgₚ 𝒳)(𝒫ᴮ : Coalgₚ 𝒫)(𝒴ᴮ : Coalgₚ 𝒴)
                   (f : 𝒳 ⇾̣ 〖 𝒫 , 𝒴 〗) : Set where
  private module 𝒳 = Coalgₚ 𝒳ᴮ
  private module 𝒫 = Coalgₚ 𝒫ᴮ
  private module 𝒴 = Coalgₚ 𝒴ᴮ

  -- Interaction between the point and renaming of all three coalgebras
  field
    r∘f : {σ : Γ ~[ 𝒫 ]↝ Δ}{ϱ : Δ ↝ Θ}{t : 𝒳 α Γ}
        → 𝒴.r (f t σ) ϱ ≡ f t (λ v → 𝒫.r (σ v) ϱ)

    f∘r : {ρ : Γ ↝ Δ}{ς : Δ ~[ 𝒫 ]↝ Θ}{t : 𝒳 α Γ}
        → f (𝒳.r t ρ) ς ≡ f t (ς ∘ ρ)

    f∘η : {v : ℐ α Γ} → f (𝒳.η v) 𝒫.η ≡ 𝒴.η v

  -- Codomain of coalgebraic map is a pointed coalgebra
  〖𝒫,𝒴〗ᴮ : Coalgₚ 〖 𝒫 , 𝒴 〗
  〖𝒫,𝒴〗ᴮ = record
    { ᵇ = record { r = λ h ρ σ → h (σ ∘ ρ) ; counit = refl ; comult = refl }
    ; η = λ v σ → f (𝒳.η v) σ
    ; r∘η = dext (λ σ → trans (sym f∘r) (congr 𝒳.r∘η (λ - → f - σ))) }

  -- The map is a pointed coalgebra homomorphism
  ᴮ⇒ : Coalgₚ⇒ 𝒳ᴮ 〖𝒫,𝒴〗ᴮ f
  ᴮ⇒ = record { ᵇ⇒ = record { ⟨r⟩ = dext′ f∘r } ; ⟨η⟩ = refl }

  -- Equality of two substitutions at the new index extends to equality of
  -- transforming new variables with the substitution
  eq-at-new : {σ : α ∙ Γ ~[ 𝒫 ]↝ α ∙ Θ}
              {ς : α ∙ Δ ~[ 𝒫 ]↝ α ∙ Θ}
           → σ new ≡ ς new
           → f (𝒳.η new) σ ≡ f (𝒳.η new) ς
  eq-at-new {σ = σ} {ς} eq = begin
         f (𝒳.η new) σ           ≡⟨⟩
         f (𝒳.η (ι new)) σ      ≡˘⟨ cong (λ - → f - σ) (𝒳.r∘η) ⟩
         f (𝒳.r (𝒳.η new) ι) σ  ≡⟨ f∘r ⟩
         f (𝒳.η new) (σ ∘ ι)    ≡⟨ cong (f (𝒳.η new)) (dext (λ{ new → eq })) ⟩
         f (𝒳.η new) (ς ∘ ι)    ≡˘⟨ f∘r ⟩
         f (𝒳.r (𝒳.η new) ι) ς  ≡⟨ cong (λ - → f - ς) (𝒳.r∘η) ⟩
         f (𝒳.η (ι new)) ς      ≡⟨⟩
         f (𝒳.η new) ς          ∎
    where
    open ≡-Reasoning
    open Coalgₚ
    ι : (α ∙ ∅) ↝ (α ∙ Δ)
    ι new = new

-- Application for a pointed coalgebra is coalgebraic
jᶜ : (𝒳ᴮ : Coalgₚ 𝒳) → Coalgebraic ℐᴮ 𝒳ᴮ 𝒳ᴮ (j 𝒳)
jᶜ 𝒳ᴮ = record { r∘f = refl ; f∘r = refl ; f∘η = refl }

-- Renaming of pointed coalgebr is coalgebraic
rᶜ : (𝒳ᴮ : Coalgₚ 𝒳) → Coalgebraic 𝒳ᴮ ℐᴮ 𝒳ᴮ (Coalgₚ.r 𝒳ᴮ)
rᶜ 𝒳ᴮ = record { r∘f = sym comult ; f∘r = sym comult ; f∘η = r∘η }
  where open Coalgₚ 𝒳ᴮ
