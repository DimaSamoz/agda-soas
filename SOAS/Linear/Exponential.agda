
-- Linear exponential of families
module SOAS.Linear.Exponential {T : Set} where

open import SOAS.Common
open import SOAS.Families.Core {T}
open import SOAS.Context
open import SOAS.Sorting
open import SOAS.Variable
open import SOAS.ContextMaps.Combinators
open import SOAS.ContextMaps.CategoryOfRenamings

open import SOAS.Linear.Tensor

open import SOAS.Families.Discrete

private
  variable
    X Y : Family
    𝒳 𝒴 𝒵 𝒲 : Familyₛ
    Γ Δ Θ Ξ : Ctx
    α τ : T

-- Day exponential of families
_⊸ᵤ_ : Family → Family → Family
(X ⊸ᵤ Y) Γ = {Δ : Ctx} → X Δ → Y (Γ ∔ Δ)

-- Mixed sorted-unsorted linear exponentials
_⊸_ : Family → Familyₛ → Familyₛ
_⊸_ = sortedᵣ _⊸ᵤ_
infixr 20 _⊸_


[_⊸_] : Familyₛ → Familyₛ → Family
[ 𝒳 ⊸ 𝒴 ] Γ = {τ : T}{Δ : Ctx} → 𝒳 τ Δ → 𝒴 τ (Δ ∔ Γ)

-- Linear application map
lap : (𝒴 : Familyₛ) → 𝒳 ⇾̣ [ 𝒳 ⊸ 𝒴 ] ⊸ 𝒴
lap 𝒴 y ζ = ζ y

-- Linear composition
L⊸ : (X Y : Family)(𝒵 : Familyₛ) → (Y ⊸ 𝒵) ⇾̣ ((X ⊸ᵤ Y) ⊸ (X ⊸ 𝒵))
L⊸ X Y 𝒵 {Γ = Γ} l {Δ} m {Θ} x = assocˡ 𝒵 Γ Δ Θ (l (m x))

L⊸-nat : (f : 𝒵 ⇾̣ 𝒲) → (l : (Y ⊸ 𝒵) α Γ)(m : (X ⊸ᵤ Y) Δ)(x : X Θ)
       → f (L⊸ X Y 𝒵 l m x)
       ≡ L⊸ X Y 𝒲 (f ∘ l) m x
L⊸-nat {Γ = Γ}{Δ = Δ}{Θ = Θ} f l m x rewrite ∔-assoc Γ Δ Θ = refl

-- Swap of linear arguments
sw : X ⊸ᵤ [ 𝒴 ⊸ 𝒵 ] ⇾ [ 𝒴 ⊸ (X ⊸ 𝒵) ]
sw {𝒵 = 𝒵}{Γ = Γ} l {Δ = Δ} y {Θ} x = assocˡ 𝒵 Δ Γ Θ (l x y)


-- Variables can be linearly parametrised by a family
κ° : (X : Family) → ℐ ⇾̣ (X ⊸ ℐ)
κ° X {Γ = Γ} y x = inl Γ y

-- Copairing and linear exponentials
copair° : (Γ {Δ} : Ctx){f : Γ ~[ X ⊸ 𝒴 ]↝ Θ}{g : Δ ~[ X ⊸ 𝒴 ]↝ Θ}{x : X Ξ}(v : ℐ α (Γ ∔ Δ))
        → copair (X ⊸ 𝒴) f g v x
        ≡ copair 𝒴 (λ v → f v x) (λ v → g v x) v
copair° ∅ v = refl
copair° (α ∙ Γ) new = refl
copair° (α ∙ Γ) {f = f} (old v) = copair° Γ {f = f ∘ old} v


-- | Monoidal closed structure

-- Linear composition
comp° : (𝒳 𝒴 𝒵 : Familyₛ) → [ 𝒳 ⊸ 𝒴 ] ⊗ [ 𝒴 ⊸ 𝒵 ] ⇾ [ 𝒳 ⊸ 𝒵 ]
comp° 𝒳 𝒴 𝒵 (_⊹_ {Γ}{Δ} l k) {_}{Θ} x = assocʳ 𝒵 Θ Γ Δ (k (l x))

comp°≈ : {p₁ p₂ : ([ 𝒳 ⊸ 𝒴 ] ⊗ [ 𝒴 ⊸ 𝒵 ]) Γ}{x : 𝒳 α Δ}
      → (eq : p₁ ≡ p₂)
      → comp° 𝒳 𝒴 𝒵 p₁ x ≡ comp° 𝒳 𝒴 𝒵 p₂ x
comp°≈ refl = refl

-- Linear currying
curry° : (𝒵 : Familyₛ) → ((X ⊗ Y) ⊸ 𝒵) ⇾̣ (X ⊸ (Y ⊸ 𝒵))
curry° 𝒵 {Γ = Γ} l {Δ} x {Θ} y = assocˡ 𝒵 Γ Δ Θ (l (x ⊹ y))

curry°≈₁ : {l₁ l₂ : ((X ⊗ Y) ⊸ 𝒵) α Γ}{x : X Δ}{y : Y Θ}
        → (eq : {Δ : Ctx} → (p : (X ⊗ Y) Δ) → l₁ p ≡ l₂ p)
        → curry° 𝒵 l₁ x y ≡ curry° 𝒵 l₂ x y
curry°≈₁ {l₁ = l₁}{l₂}{x}{y} eq rewrite eq (x ⊹ y) = refl

curry°-nat₃ : (f : 𝒵 ⇾̣ 𝒲)
           → (l : ((X ⊗ Y) ⊸ 𝒵) α Γ)(x : X Δ)(y : Y Θ)
           → f (curry° 𝒵 l x y)
           ≡ curry° 𝒲 (f ∘ l) x y
curry°-nat₃ {Γ = Γ}{Δ}{Θ} f l x y rewrite ∔-assoc Γ Δ Θ = refl
