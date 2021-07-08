
-- Box modality: cofree presheaf on a family
module SOAS.Abstract.Box {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Sorting
open import SOAS.Variable
open import SOAS.Families.Core {T}
open import SOAS.Families.Isomorphism
open import SOAS.Families.BCCC using (_×ₘ_; _+ₘ_; _⇨_; _⇨̣_)

open import SOAS.Abstract.Hom


open import Categories.Functor.Bifunctor

module Unsorted where
  -- Box modality: the skew-closed action of variables on a family
  □ : Family → Family
  □ X = ⟨ ℐ , X ⟩

  -- □ is an endofunctor on families
  □F : Functor 𝔽amilies 𝔽amilies
  □F = appˡ ⟨-,-⟩F ℐ


  -- | Properties of □

  private
    variable
      X Y : Family

  -- | □ preserves products of families
  □[X×Y]≅□X×□Y : □ (X ×ₘ Y) ≅ₘ (□ X ×ₘ □ Y)
  □[X×Y]≅□X×□Y = ⟨𝒳,Y×Z⟩≅⟨𝒳,Y⟩×⟨𝒳,Z⟩

  -- □ can be factored out from a sum
  □X+□Y⇾□[X+Y] : (□ X +ₘ □ Y) ⇾ □ (X +ₘ Y)
  □X+□Y⇾□[X+Y] = ⟨𝒳,Y⟩+⟨𝒳,Z⟩⇾⟨𝒳,Y+Z⟩


module Sorted where

  -- Sorted box modality: the skew-closed hom of variables and a family
  □ : Familyₛ → Familyₛ
  □ X = 〖 ℐ , X 〗

  -- □ is an endofunctor on families
  □F : Functor 𝔽amiliesₛ 𝔽amiliesₛ
  □F = appˡ 〖-,-〗F ℐ

  □₁ : {X Y : Familyₛ} → (X ⇾̣ Y) → □ X ⇾̣ □ Y
  □₁ f x ρ = f (x ρ)

  ζ : (X : Familyₛ) → □ X ⇾̣ □ (□ X)
  ζ X b ρ ϱ = b (ϱ ∘ ρ)
