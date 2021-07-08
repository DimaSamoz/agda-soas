

-- Bi-Cartesian closed structure of families
module SOAS.Families.BCCC {T : Set} where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Sorting {T}
open import SOAS.Families.Core {T}
open import SOAS.Families.Isomorphism {T}

import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.CartesianClosed as CCC
import Categories.Category.Cartesian as Cart
open import Categories.Category.Cocartesian
open import Categories.Category.BicartesianClosed
import Categories.Object.Initial as Initial
open import Categories.Category.Monoidal


import Data.Unit as Unit
import Data.Empty as Empty


-- | Unsorted

-- Category of families is Cartesian closed
𝔽am-CanCCC : Canonical.CartesianClosed 𝔽amilies
𝔽am-CanCCC = record
  { ⊤ = λ Γ → Unit.⊤
  ; _×_ = λ X Y Γ → X Γ × Y Γ
  ; ! = λ _ → Unit.tt
  ; π₁ = proj₁
  ; π₂ = proj₂
  ; ⟨_,_⟩ = λ f g x → f x , g x
  ; !-unique = λ f → refl
  ; π₁-comp = refl
  ; π₂-comp = refl
  ; ⟨,⟩-unique = λ p₁ p₂ {Γ}{x} → sym (cong₂ _,_ p₁ p₂)
  ; _^_ = λ X Y Γ → Y Γ → X Γ
  ; eval = λ{ (f , x) → f x}
  ; curry = λ f x y → f (x , y)
  ; eval-comp = refl
  ; curry-resp-≈ = λ{X}{Y}{Z}{f}{g} p → ext (λ x → p)
  ; curry-unique = λ p → ext (λ x → p)
  }

𝔽am-CCC : CCC.CartesianClosed 𝔽amilies
𝔽am-CCC = Canonical.Equivalence.fromCanonical _ 𝔽am-CanCCC
module 𝔽am-CCC = CCC.CartesianClosed 𝔽am-CCC

-- Category of families is co-Cartesian
𝔽am-Cocartesian : Cocartesian 𝔽amilies
𝔽am-Cocartesian = record
  { initial = record { ⊥ = λ Γ → Empty.⊥ ; ⊥-is-initial = record { ! = λ () ; !-unique = λ{ f  {Γ} {()}} } }
  ; coproducts = record { coproduct = λ{X}{Y} → record
    { A+B = λ Γ → X Γ ⊎ Y Γ
    ; i₁ = inj₁
    ; i₂ = inj₂
    ; [_,_] = λ{ f g (inj₁ x) → f x ; f g (inj₂ y) → g y}
    ; inject₁ = refl
    ; inject₂ = refl
    ; unique = λ{ p₁ p₂ {Γ} {inj₁ x} → sym p₁ ; p₁ p₂ {Γ} {inj₂ y} → sym p₂}
    } }
  }
module 𝔽am-Cocart = Cocartesian 𝔽am-Cocartesian

-- Category of families is bi-Cartesian closed
𝔽am-BCCC : BicartesianClosed 𝔽amilies
𝔽am-BCCC = record { cartesianClosed = 𝔽am-CCC ; cocartesian = 𝔽am-Cocartesian }

module 𝔽am-BCCC = BicartesianClosed 𝔽am-BCCC

-- Shorthand for family product and sum and exponential
_×ₘ_ : Family → Family → Family
_×ₘ_ = 𝔽am-CCC._×_

_+ₘ_ : Family → Family → Family
_+ₘ_ = 𝔽am-Cocart._+_

_⇨_ : Family → Family → Family
_⇨_ = 𝔽am-CCC._⇨_
infixr 25 _⇨_

⊤ₘ : Family
⊤ₘ Γ = Unit.⊤

private variable X Y Z W : Family

curryₘ-iso : (X ×ₘ Y ⇾ Z) ≅ₛ (X ⇾ Y ⇨ Z)
curryₘ-iso = record
  { from = λ f x y → f (x , y)
  ; to = λ{ f (x , y) → f x y }
  ; iso = record { isoˡ = refl ; isoʳ = refl }
  }

-- Congruence for indexed families of functions
⇾-cong : X ≅ₘ Y → W ≅ₘ Z → (X ⇾ W) ≅ₛ (Y ⇾ Z)
⇾-cong X≅Y W≅Z = record
  { from = λ f y → _≅ₘ_.from W≅Z (f (_≅ₘ_.to X≅Y y))
  ; to = λ g x → _≅ₘ_.to W≅Z (g (_≅ₘ_.from X≅Y x))
  ; iso = record
    { isoˡ = λ {f} → dext′ (trans (_≅ₘ_.isoˡ W≅Z) (cong f (_≅ₘ_.isoˡ X≅Y)))
    ; isoʳ = λ {g} → dext′ (trans (_≅ₘ_.isoʳ W≅Z) (cong g (_≅ₘ_.isoʳ X≅Y)))
    }
  }

⇾-≅dom : X ≅ₘ Y → (X ⇾ W) ≅ₛ (Y ⇾ W)
⇾-≅dom X≅Y = ⇾-cong X≅Y ≅ₘ.refl

⇾-≅cod : W ≅ₘ Z → (X ⇾ W) ≅ₛ (X ⇾ Z)
⇾-≅cod W≅Z = ⇾-cong ≅ₘ.refl W≅Z


-- | Sorted

-- Category of sorted families is Cartesian closed
𝔽amₛ-CanCCC : Canonical.CartesianClosed 𝔽amiliesₛ
𝔽amₛ-CanCCC = 𝕊orted-CanCCC 𝔽am-CanCCC

𝔽amₛ-CCC : CCC.CartesianClosed 𝔽amiliesₛ
𝔽amₛ-CCC = Canonical.Equivalence.fromCanonical _ 𝔽amₛ-CanCCC

-- Category of sorted families is co-Cartesian
𝔽amₛ-Cocartesian : Cocartesian 𝔽amiliesₛ
𝔽amₛ-Cocartesian = 𝕊orted-Cocartesian 𝔽am-Cocartesian

-- Category of sorted families is bi-Cartesian closed
𝔽amₛ-BCCC : BicartesianClosed 𝔽amiliesₛ
𝔽amₛ-BCCC = 𝕊orted-BCCC 𝔽am-BCCC

module 𝔽amₛ-CCC = CCC.CartesianClosed 𝔽amₛ-CCC
module 𝔽amₛ-Cocart = Cocartesian 𝔽amₛ-Cocartesian

𝔽amₛ-Mon : Monoidal 𝔽amiliesₛ
𝔽amₛ-Mon = Cart.CartesianMonoidal.monoidal 𝔽amiliesₛ 𝔽amₛ-CCC.cartesian

-- Shorthand for sorted family product and sum and exponential
_×̣ₘ_ : Familyₛ → Familyₛ → Familyₛ
_×̣ₘ_ = 𝔽amₛ-CCC._×_

_+̣ₘ_ : Familyₛ → Familyₛ → Familyₛ
_+̣ₘ_ = 𝔽amₛ-Cocart._+_

_⇨̣_ : Familyₛ → Familyₛ → Familyₛ
_⇨̣_ = 𝔽amₛ-CCC._⇨_
infixr 25 _⇨̣_
