
-- Families are a presheaf on the discrete category of contexts
module SOAS.Families.Discrete {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Sorting
-- open import SOAS.Construction.Structure
open import SOAS.Families.Core {T}
open import SOAS.Abstract.Hom {T}
import SOAS.Families.Delta {T} as δ ; open δ.Sorted

private
  variable
    α τ : T
    Γ Δ Θ Ξ : Ctx

-- Lift context equality to mapping
≡map : (𝒳 : Familyₛ) → (Γ ≡ Δ) → 𝒳 α Γ → 𝒳 α Δ
≡map {Γ} {.Γ} 𝒳 refl x = x

-- Inverse
≡map-inv : (𝒳 : Familyₛ)(p : Γ ≡ Δ)(x : 𝒳 α Γ)
          → ≡map 𝒳 (sym p) (≡map 𝒳 p x) ≡ x
≡map-inv 𝒳 refl x = refl

-- Equational associativity
assocˡ : (𝒳 : Familyₛ)(Γ Δ Θ : Ctx) → 𝒳 α (Γ ∔ (Δ ∔ Θ)) → 𝒳 α ((Γ ∔ Δ) ∔ Θ)
assocˡ 𝒳 Γ Δ Θ x = ≡map 𝒳 (sym (∔-assoc Γ Δ Θ)) x

assocʳ : (𝒳 : Familyₛ)(Γ Δ Θ : Ctx) → 𝒳 α ((Γ ∔ Δ) ∔ Θ) → 𝒳 α (Γ ∔ (Δ ∔ Θ))
assocʳ 𝒳 Γ Δ Θ x = ≡map 𝒳 (∔-assoc Γ Δ Θ) x

assocˡʳ-inv : (𝒳 : Familyₛ)(Γ Δ Θ  : Ctx) → (x : 𝒳 α ((Γ ∔ Δ) ∔ Θ))
            → assocˡ 𝒳 Γ Δ Θ (assocʳ 𝒳 Γ Δ Θ x) ≡ x
assocˡʳ-inv 𝒳 Γ Δ Θ x = ≡map-inv 𝒳 (∔-assoc Γ Δ Θ) x

-- Naturality
assocˡ-nat : {𝒳 𝒴 : Familyₛ}(Γ : Ctx)(f : 𝒳 ⇾̣ 𝒴)(x : 𝒳 α (Γ ∔ (Δ ∔ Θ)))
           → f (assocˡ 𝒳 Γ Δ Θ x) ≡ assocˡ 𝒴 Γ Δ Θ (f x)
assocˡ-nat {Δ = Δ}{Θ} Γ f x rewrite ∔-assoc Γ Δ Θ = refl

-- Interaction of associator and internal homs
assocˡ-hom₁ : (𝒳 𝒴 : Familyₛ)(Δ : Ctx)(h : 〖 𝒳 , 𝒴 〗 α Γ){σ : Γ ~[ 𝒳 ]↝ (Δ ∔ (Θ ∔ Ξ))}
     → assocˡ 𝒴 Δ Θ Ξ (h σ)
     ≡ h (assocˡ 𝒳 Δ Θ Ξ ∘ σ)
assocˡ-hom₁ {Θ = Θ}{Ξ} 𝒳 𝒴 Δ h rewrite ∔-assoc Δ Θ Ξ = refl

assocˡ-hom₂ : ({𝒳} 𝒴 : Familyₛ)(Γ {Δ Θ Ξ} : Ctx)(h : 〖 𝒳 , 𝒴 〗 α (Γ ∔ (Δ ∔ Θ)))(σ : ((Γ ∔ Δ) ∔ Θ) ~[ 𝒳 ]↝ Ξ)
         → assocˡ 〖 𝒳 , 𝒴 〗 Γ Δ Θ h σ
         ≡ h (σ ∘ assocˡ ℐ Γ Δ Θ)
assocˡ-hom₂ 𝒴 Γ {Δ}{Θ} h σ rewrite ∔-assoc Γ Δ Θ = refl
