
-- Linear monoidal closed structure for families
module SOAS.Families.Linear {T : Set} where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Sorting {T}
open import SOAS.Families.Core {T}
open import SOAS.Families.Isomorphism {T}


open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Closed
open import Categories.Functor.Bifunctor

-- | Monoidal tensor and unit

-- Linear tensor product that combines two families with two disjoint contexts
data _⊗_ (X Y : Family) : Ctx → Set where
  merge : (Γ Δ : Ctx) → X Γ → Y Δ → (X ⊗ Y) (Δ ∔ Γ)
infixr 20 _⊗_

pattern _⊹_ {Γ}{Δ} t s = merge Γ Δ t s
infix 30 _⊹_

-- ⊗ is a bifunctor
⊗F : Bifunctor 𝔽amilies 𝔽amilies 𝔽amilies
⊗F = record
  { F₀ = λ (X , Y) → X ⊗ Y
  ; F₁ = λ{ {X , Y}{X′ , Y′} (f , g) (x ⊹ y) → (f x) ⊹ (g y)}
  ; identity = λ{ {X , Y}{Γ}{x ⊹ y} → refl }
  ; homomorphism = λ{ {X , Y}{X′ , Y′}{X″ , Y″}{f , g}{f′ , g′}{Γ}{x ⊹ y} → refl }
  ; F-resp-≈ = λ{ (p₁ , p₂) {.(Δ ∔ Γ)} {merge Γ Δ t s} → cong₂ (merge Γ Δ) p₁ p₂ }
  }

_⊗̣_ : Familyₛ → Familyₛ → Familyₛ
_⊗̣_ = sorted₂ _⊗_

𝒚 : Ctx → Family
𝒚 Γ Δ = Γ ≡ Δ

-- Family which is only inhabited at the empty context
E : Family
E = 𝒚 ∅

-- Sorted family which is only inhabited at a singleton context
N : Familyₛ
N α = 𝒚 ⌈ α ⌋

-- | Monoidal exponential

-- Linear exponential between families
_⊸_ : Family → Family → Family
(X ⊸ Y) Γ = {Δ : Ctx} → X Δ → Y (Δ ∔ Γ)
infixr 15 _⊸_

-- Linear exponential between sorted families
_⊸∙_ : Familyₛ → Familyₛ → Familyₛ
_⊸∙_ = sorted₂ _⊸_
infixr 15 _⊸∙_

-- ⊸ is a bifunctor
⊸F : Bifunctor 𝔽am.op 𝔽amilies 𝔽amilies
⊸F = record
  { F₀ = λ (X , Y) → X ⊸ Y
  ; F₁ = λ{ {X , Y}{X′ , Y′} (f , g) e x → g (e (f x))}
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ{ {X , Y}{X′ , Y′}{f , g} (p₁ , p₂) {Γ}{e} →
                      dext′ (trans (cong (g ∘ e) p₁) p₂) }
  }
