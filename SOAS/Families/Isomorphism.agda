
-- Isomorphism of indexed families
module SOAS.Families.Isomorphism {T} where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Families.Core {T}

open import Categories.Morphism 𝔽amilies public using ()
        renaming ( _≅_ to _≅ₘ_ ; module ≅ to ≅ₘ ; ≅-setoid to ≅ₘ-setoid)

-- Isomorphism between two families
record FamIso (X Y : Family) : Set where

  -- Prove isomorphism of the families X and Y in the category 𝔽am from
  -- a proof of isomorphism of the sets X Γ and Y Γ for all contexts Γ.
  field iso : (Γ : Ctx) → X Γ ≅ₛ Y Γ

  -- Two directions of the isomorphism.
  iso⇒ : X ⇾ Y
  iso⇒ {Γ} = _≅ₛ_.from (iso Γ)
  iso⇐ : Y ⇾ X
  iso⇐ {Γ} = _≅ₛ_.to (iso Γ)

  -- Construct the isomorphism of families
  ≅ₘ : X ≅ₘ Y
  ≅ₘ = record
    { from = iso⇒
    ; to = iso⇐
    ; iso = record
      { isoˡ = λ {Γ}{x} → _≅ₛ_.isoˡ (iso Γ)
      ; isoʳ = λ {Γ}{x} → _≅ₛ_.isoʳ (iso Γ)
      }
    }

≅ₘ→FamIso : {X Y : Family} → X ≅ₘ Y → FamIso X Y
≅ₘ→FamIso p = record { iso = λ Γ → record
  { from = _≅ₘ_.from p
  ; to = _≅ₘ_.to p
  ; iso = record { isoˡ = _≅ₘ_.isoˡ p ; isoʳ = _≅ₘ_.isoʳ p }
  } }

-- | Isomorphism of sorted families

open import Categories.Morphism 𝔽amiliesₛ public
  using () renaming ( _≅_ to _≅̣ₘ_ ; module ≅ to ≅̣ₘ)

-- Sorted family isomorphism gives a family isomorphism at each sort
≅̣ₘ→≅ₘ : {τ : T}{𝒳 𝒴 : Familyₛ} → 𝒳 ≅̣ₘ 𝒴 → 𝒳 τ ≅ₘ 𝒴 τ
≅̣ₘ→≅ₘ {τ} p = record { from = _≅̣ₘ_.from p ; to = _≅̣ₘ_.to p
                     ; iso = record { isoˡ = _≅̣ₘ_.isoˡ p ; isoʳ = _≅̣ₘ_.isoʳ p } }

-- Family isomorphism at each sort gives sorted family isomorphism
≅ₘ→≅̣ₘ : {𝒳 𝒴 : Familyₛ} → ({τ : T} → 𝒳 τ ≅ₘ 𝒴 τ) → 𝒳 ≅̣ₘ 𝒴
≅ₘ→≅̣ₘ p = record { from = _≅ₘ_.from p ; to = _≅ₘ_.to p
                 ; iso = record { isoˡ = _≅ₘ_.isoˡ p ; isoʳ = _≅ₘ_.isoʳ p } }
