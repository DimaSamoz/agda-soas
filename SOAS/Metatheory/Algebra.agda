

open import SOAS.Common
open import SOAS.Families.Core

-- Algebras for a signature endofunctor
module SOAS.Metatheory.Algebra {T : Set} (⅀F : Functor (𝔽amiliesₛ {T}) (𝔽amiliesₛ {T})) where


module ⅀ = Functor ⅀F

⅀ : Familyₛ → Familyₛ
⅀ = ⅀.₀

⅀₁ : {𝒳 𝒴 : Familyₛ} → 𝒳 ⇾̣ 𝒴 → ⅀ 𝒳 ⇾̣ ⅀ 𝒴
⅀₁ = Functor.₁ ⅀F
