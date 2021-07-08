
-- Category of indexed families
module SOAS.Families.Core {T : Set} where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Sorting {T}


-- | Unsorted

-- Sets indexed by a context
Family : Set₁
Family = Ctx → Set

-- Indexed functions between families
_⇾_ : Family → Family → Set
X ⇾ Y = ∀{Γ : Ctx} → X Γ → Y Γ
infixr 10 _⇾_

-- Category of indexed families of sets and indexed functions between them
𝔽amilies : Category 1ℓ 0ℓ 0ℓ
𝔽amilies = categoryHelper record
  { Obj = Family
  ; _⇒_ = _⇾_
  ; _≈_ = λ {X}{Y} f g → ∀{Γ : Ctx}{x : X Γ} → f x ≡ g x
  ; id = id
  ; _∘_ = λ g f → g ∘ f
  ; assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; equiv = record { refl = refl ; sym = λ p → sym p ; trans = λ p q → trans p q }
  ; ∘-resp-≈ = λ where {f = f} p q → trans (cong f q) p
  }
module 𝔽am = Category 𝔽amilies


-- | Sorted

-- Category of sorted families
𝔽amiliesₛ : Category 1ℓ 0ℓ 0ℓ
𝔽amiliesₛ = 𝕊orted 𝔽amilies
module 𝔽amₛ = Category 𝔽amiliesₛ

-- Type of sorted families
Familyₛ : Set₁
Familyₛ = 𝔽amₛ.Obj

-- Maps between sorted families
_⇾̣_ : Familyₛ → Familyₛ → Set
_⇾̣_ = 𝔽amₛ._⇒_
infixr 10 _⇾̣_

-- Turn sorted family into unsorted by internally quantifying over the sort
∀[_] : Familyₛ → Family
∀[ 𝒳 ] Γ = {τ : T} → 𝒳 τ Γ

-- Maps between Familyₛ functors
_⇾̣₂_ : (Familyₛ → Familyₛ) → (Familyₛ → Familyₛ) → Set₁
(𝓧 ⇾̣₂ 𝓨) = {𝒵 : Familyₛ} → 𝓧 𝒵 ⇾̣ 𝓨 𝒵
