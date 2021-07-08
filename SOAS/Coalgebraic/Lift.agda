
-- Lifting of substitutions, and instance of strength for δ
module SOAS.Coalgebraic.Lift {T : Set} where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Variable
open import SOAS.Families.Core {T}
import SOAS.Families.Delta {T} as δ; open δ.Sorted
open import SOAS.Abstract.Hom {T}
import SOAS.Abstract.Box {T} as □ ; open □.Sorted
import SOAS.Abstract.Coalgebra {T} as →□ ; open →□.Sorted

open import SOAS.Coalgebraic.Map
open import SOAS.Coalgebraic.Strength

private
  variable
    Γ Δ Θ : Ctx
    α : T

module _ {𝒫 : Familyₛ} (𝒫ᴮ : Coalgₚ 𝒫) where
  open Coalgₚ 𝒫ᴮ

  -- General lifting over an arbitrary context
  lift : (Ξ : Ctx) → Γ ~[ 𝒫 ]↝ Δ → (Ξ ∔ Γ) ~[ 𝒫 ]↝ (Ξ ∔ Δ)
  lift ∅ σ v             = σ v
  lift (τ ∙ Ξ) σ new     = η new
  lift (τ ∙ Ξ) σ (old v) = r (lift Ξ σ v) old

  -- Single-variable lifting
  lift₁ : {τ : T} → Γ ~[ 𝒫 ]↝ Δ → (τ ∙ Γ) ~[ 𝒫 ]↝ (τ ∙ Δ)
  lift₁ {τ = τ} = lift ⌈ τ ⌋

-- General lifting of renaming
rlift : (Ξ : Ctx) → Γ ↝ Δ → (Ξ ∔ Γ) ↝ (Ξ ∔ Δ)
rlift Ξ = lift ℐᴮ Ξ

-- Strength for context extension
δ:Strength : (Ξ : Ctx) → Strength (δF Ξ)
δ:Strength Ξ = record
  { str = λ 𝒫ᴮ 𝒳 h σ → h (lift 𝒫ᴮ Ξ σ)
  ; str-nat₁ = λ fᴮ⇒ h σ → cong h (dext (str-nat₁ Ξ fᴮ⇒ σ))
  ; str-nat₂ = λ f h σ → refl
  ; str-unit = λ 𝒳 h → cong h (dext (str-unit Ξ 𝒳))
  ; str-assoc = λ 𝒳 fᶜ h σ ς → cong h (dext (str-assoc Ξ 𝒳 fᶜ σ ς))
  }
  where
  open ≡-Reasoning
  open Coalgₚ
  open Coalgₚ⇒

  str-nat₁ : (Ξ : Ctx){𝒫 𝒬 : Familyₛ} {𝒫ᴮ : Coalgₚ 𝒫}
             {𝒬ᴮ : Coalgₚ 𝒬} {f : 𝒬 ⇾̣ 𝒫}
           → Coalgₚ⇒ 𝒬ᴮ 𝒫ᴮ f
           → (σ : Γ ~[ 𝒬 ]↝ Δ)(v : ℐ α (Ξ ∔ Γ))
    → lift 𝒫ᴮ Ξ (f ∘ σ) v
    ≡ f (lift 𝒬ᴮ Ξ σ v)
  str-nat₁ ∅ fᴮ⇒ σ v = refl
  str-nat₁ (α ∙ Ξ) {𝒫ᴮ = 𝒫ᴮ} fᴮ⇒ σ new = sym (Coalgₚ⇒.⟨η⟩ fᴮ⇒)
  str-nat₁ (α ∙ Ξ) {𝒫ᴮ = 𝒫ᴮ} {𝒬ᴮ}{f}fᴮ⇒ σ (old v) = begin
       lift 𝒫ᴮ (α ∙ Ξ) (f ∘ σ) (old v)
     ≡⟨ congr (str-nat₁ Ξ fᴮ⇒ σ v) (λ - → r 𝒫ᴮ - old) ⟩
       r 𝒫ᴮ (f (lift 𝒬ᴮ Ξ σ v)) old
     ≡˘⟨ ⟨r⟩ fᴮ⇒ ⟩
       f (lift 𝒬ᴮ (α ∙ Ξ) σ (old v))
     ∎

  str-unit : (Ξ : Ctx) (𝒳 : Familyₛ) (v : ℐ α (Ξ ∔ Γ))
    → lift ℐᴮ Ξ id v ≡ v
  str-unit ∅ 𝒳 v = refl
  str-unit (α ∙ Ξ) 𝒳 new = refl
  str-unit (α ∙ Ξ) 𝒳 (old v) = cong old (str-unit Ξ 𝒳 v)

  str-assoc : (Ξ : Ctx) (𝒳 : Familyₛ) {𝒫 𝒬 ℛ : Familyₛ}
              {𝒫ᴮ : Coalgₚ 𝒫} {𝒬ᴮ : Coalgₚ 𝒬} {ℛᴮ : Coalgₚ ℛ}
              {f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗}
              (fᶜ : Coalgebraic 𝒫ᴮ 𝒬ᴮ ℛᴮ f) (open Coalgebraic fᶜ)
              (σ : Γ ~[ 𝒫 ]↝ Δ) (ς : Δ ~[ 𝒬 ]↝ Θ)(v : ℐ α (Ξ ∔ Γ))
    → lift ℛᴮ Ξ (λ u → f (σ u) ς) v
    ≡ lift 〖𝒫,𝒴〗ᴮ Ξ (f ∘ σ) v (lift 𝒬ᴮ Ξ ς)
  str-assoc ∅ 𝒳 fᶜ σ ς v = refl
  str-assoc (β ∙ Ξ) 𝒳 {𝒫ᴮ = 𝒫ᴮ}{𝒬ᴮ}{ℛᴮ} {f} fᶜ σ ς new = begin
       η ℛᴮ new                          ≡˘⟨ f∘η ⟩
       f (η 𝒫ᴮ new) (η 𝒬ᴮ)               ≡⟨ eq-at-new refl ⟩
       f (η 𝒫ᴮ new) (lift 𝒬ᴮ (β ∙ Ξ) ς)  ∎
     where open Coalgebraic fᶜ

  str-assoc {Γ = Γ} (β ∙ Ξ)  𝒳 {𝒫 = 𝒫}{𝒬}{𝒫ᴮ = 𝒫ᴮ}{𝒬ᴮ}{ℛᴮ}{f} fᶜ σ ς (old v) =
     begin
         r ℛᴮ   (lift ℛᴮ Ξ (λ u → f (σ u) ς) v)   old
     ≡⟨ congr (str-assoc Ξ 𝒳 fᶜ σ ς v) (λ - → r ℛᴮ - old) ⟩
         r ℛᴮ (  lift 〖𝒫,𝒴〗ᴮ Ξ (f ∘ σ) v   (lift 𝒬ᴮ Ξ ς)) old
     ≡⟨ congr (str-nat₁ Ξ fᴮ⇒ (σ) v) (λ - → r ℛᴮ (- (lift 𝒬ᴮ Ξ ς)) old) ⟩
         r ℛᴮ (f (lift 𝒫ᴮ Ξ σ v) (lift 𝒬ᴮ Ξ ς)) old
     ≡⟨ r∘f ⟩
         f (lift 𝒫ᴮ Ξ σ v)   (λ u → r 𝒬ᴮ (lift 𝒬ᴮ Ξ ς u) old)
     ≡˘⟨ congr (str-nat₁ Ξ fᴮ⇒ σ v) (λ - → - (λ u → r 𝒬ᴮ (lift 𝒬ᴮ Ξ ς u) old)) ⟩
         lift 〖𝒫,𝒴〗ᴮ Ξ (f ∘ σ) v (λ u → r 𝒬ᴮ (lift 𝒬ᴮ Ξ ς u) old)
     ∎
     where open Coalgebraic fᶜ renaming (ᴮ⇒ to fᴮ⇒)

module δ:Str Θ = Strength (δ:Strength Θ)

-- Derived lifting properties
rlift-id : (𝒳 : Familyₛ)(Ξ : Ctx)(b : δ Ξ (□ 𝒳) α Γ)
         → b (rlift Ξ id) ≡ b id
rlift-id 𝒳 Ξ = Strength.str-unit (δ:Strength Ξ) 𝒳


lift-comp : {𝒫 𝒬 : Familyₛ}{𝒫ᴮ : Coalgₚ 𝒫}{𝒬ᴮ : Coalgₚ 𝒬}
            (𝒳 : Familyₛ)(Ξ : Ctx){f : 𝒬 ⇾̣ 𝒫}
            (fᴮ⇒ : Coalgₚ⇒ 𝒬ᴮ 𝒫ᴮ f)
            (h : δ Ξ 〖 𝒫 , 𝒳 〗 α Γ) (σ : Γ ~[ 𝒬 ]↝ Δ)
  → h (lift 𝒫ᴮ Ξ (f ∘ σ))
  ≡ h (f ∘ lift 𝒬ᴮ Ξ σ)
lift-comp 𝒳 Ξ fᴮ⇒ h σ = Strength.str-nat₁ (δ:Strength Ξ) {𝒳 = 𝒳} fᴮ⇒ h σ


lift-assoc : {𝒫 𝒬 ℛ : Familyₛ}
            {𝒫ᴮ : Coalgₚ 𝒫} {𝒬ᴮ : Coalgₚ 𝒬} {ℛᴮ : Coalgₚ ℛ}
            (𝒳 : Familyₛ)(Ξ : Ctx) {f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗}
            (fᶜ : Coalgebraic 𝒫ᴮ 𝒬ᴮ ℛᴮ f)
            (open Coalgebraic fᶜ)
            (h : δ Ξ 〖 ℛ , 𝒳 〗 α Γ)
            (σ : Γ ~[ 𝒫 ]↝ Δ) (ς : Δ ~[ 𝒬 ]↝ Θ)
  → h (lift ℛᴮ Ξ (λ v → f (σ v) ς))
  ≡ h (λ v → lift 〖𝒫,𝒴〗ᴮ Ξ (f ∘ σ) v (lift 𝒬ᴮ Ξ ς))
lift-assoc 𝒳 Ξ fᶜ h σ ς = Strength.str-assoc (δ:Strength Ξ) 𝒳 fᶜ h σ ς

lift-dist : {𝒫 𝒬 ℛ : Familyₛ}{𝒫ᴮ : Coalgₚ 𝒫}{𝒬ᴮ : Coalgₚ 𝒬}{ℛᴮ : Coalgₚ ℛ}
            (𝒳 : Familyₛ){Ξ : Ctx}{f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗}
            (fᶜ : Coalgebraic 𝒫ᴮ 𝒬ᴮ ℛᴮ f)
            (h : δ Ξ 〖 ℛ , 𝒳 〗 α Γ)
            (σ : Γ ~[ 𝒫 ]↝ Δ) (ς : Δ ~[ 𝒬 ]↝ Θ)
  → h (lift ℛᴮ Ξ (λ v → f (σ v) ς))
  ≡ h (λ v → f (lift 𝒫ᴮ Ξ σ v) (lift 𝒬ᴮ Ξ ς))
lift-dist 𝒳 {Ξ} = Strength.str-dist (δ:Strength Ξ) 𝒳
