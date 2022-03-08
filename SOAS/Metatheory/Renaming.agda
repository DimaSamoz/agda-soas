
open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Metatheory.SynAlgebra

-- Renaming structure by initiality
module SOAS.Metatheory.Renaming {T : Set}
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ) (⅀:Str : Strength ⅀F)
  (𝔛 : Familyₛ) (open SOAS.Metatheory.SynAlgebra ⅀F 𝔛)
  (𝕋:Init : Initial 𝕊ynAlgebras)
  where

open import SOAS.Context
open import SOAS.Variable
open import SOAS.Abstract.Hom
import SOAS.Abstract.Coalgebra as →□ ; open →□.Sorted
import SOAS.Abstract.Box as □ ; open □.Sorted
open import SOAS.Abstract.Monoid

open import SOAS.Coalgebraic.Map

open import SOAS.Metatheory.Algebra {T} ⅀F
open import SOAS.Metatheory.Semantics ⅀F ⅀:Str 𝔛 𝕋:Init
open import SOAS.Metatheory.Traversal ⅀F ⅀:Str 𝔛 𝕋:Init

open Strength ⅀:Str

-- Renaming is a ℐ-parametrised traversal into 𝕋
module Renaming = □Traversal 𝕋ᵃ

𝕣𝕖𝕟 : 𝕋 ⇾̣ □ 𝕋
𝕣𝕖𝕟 = Renaming.𝕥𝕣𝕒𝕧

𝕨𝕜 : {α τ : T}{Γ : Ctx} → 𝕋 α Γ → 𝕋 α (τ ∙ Γ)
𝕨𝕜 t = 𝕣𝕖𝕟 t old

-- Comultiplication law
𝕣𝕖𝕟-comp : MapEq₂ ℐᴮ ℐᴮ 𝕒𝕝𝕘 (λ t ρ ϱ → 𝕣𝕖𝕟 t (ϱ ∘ ρ))
                           (λ t ρ ϱ → 𝕣𝕖𝕟 (𝕣𝕖𝕟 t ρ) ϱ)
𝕣𝕖𝕟-comp = record
  { φ = 𝕧𝕒𝕣
  ; ϕ = λ x ρ → 𝕧𝕒𝕣 (ρ x)
  ; χ = 𝕞𝕧𝕒𝕣
  ; f⟨𝑣⟩ = 𝕥⟨𝕧⟩
  ; f⟨𝑚⟩ = 𝕥⟨𝕞⟩
  ; f⟨𝑎⟩ = λ{ {σ = ρ}{ϱ}{t} → begin
        𝕣𝕖𝕟 (𝕒𝕝𝕘 t) (ϱ ∘ ρ)
    ≡⟨ 𝕥⟨𝕒⟩ ⟩
        𝕒𝕝𝕘 (str ℐᴮ 𝕋 (⅀₁ 𝕣𝕖𝕟 t) (ϱ ∘ ρ))
    ≡⟨ cong 𝕒𝕝𝕘 (str-dist 𝕋 (jᶜ ℐᴮ) (⅀₁ 𝕣𝕖𝕟 t) ρ ϱ) ⟩
        𝕒𝕝𝕘 (str ℐᴮ 𝕋 (str ℐᴮ (□ 𝕋) (⅀₁ (precomp 𝕋 (j ℐ)) (⅀₁ 𝕣𝕖𝕟 t)) ρ) ϱ)
    ≡˘⟨ congr ⅀.homomorphism (λ - → 𝕒𝕝𝕘 (str ℐᴮ 𝕋 (str ℐᴮ (□ 𝕋) - ρ) ϱ)) ⟩
        𝕒𝕝𝕘 (str ℐᴮ 𝕋 (str ℐᴮ (□ 𝕋) (⅀₁ (λ{ t ρ ϱ → 𝕣𝕖𝕟 t (ϱ ∘ ρ)}) t) ρ) ϱ)
    ∎ }
  ; g⟨𝑣⟩ = trans (𝕥≈₁ 𝕥⟨𝕧⟩) 𝕥⟨𝕧⟩
  ; g⟨𝑚⟩ = trans (𝕥≈₁ 𝕥⟨𝕞⟩) 𝕥⟨𝕞⟩
  ; g⟨𝑎⟩ = λ{ {σ = ρ}{ϱ}{t} → begin
        𝕣𝕖𝕟 (𝕣𝕖𝕟 (𝕒𝕝𝕘 t) ρ) ϱ
    ≡⟨ 𝕥≈₁ 𝕥⟨𝕒⟩ ⟩
        𝕣𝕖𝕟 (𝕒𝕝𝕘 (str ℐᴮ 𝕋 (⅀₁ 𝕣𝕖𝕟 t) ρ)) ϱ
    ≡⟨ 𝕥⟨𝕒⟩ ⟩
        𝕒𝕝𝕘 (str ℐᴮ 𝕋 (⅀₁ 𝕣𝕖𝕟 (str ℐᴮ 𝕋 (⅀₁ 𝕣𝕖𝕟 t) ρ)) ϱ)
    ≡˘⟨ congr (str-nat₂ 𝕣𝕖𝕟 (⅀₁ 𝕣𝕖𝕟 t) ρ) (λ - → 𝕒𝕝𝕘 (str ℐᴮ 𝕋 - ϱ)) ⟩
        𝕒𝕝𝕘 (str ℐᴮ 𝕋 (str ℐᴮ (□ 𝕋) (⅀.F₁ (λ { h′ ς → 𝕣𝕖𝕟 (h′ ς) }) (⅀₁ 𝕣𝕖𝕟 t)) ρ) ϱ)
    ≡˘⟨ congr ⅀.homomorphism (λ - → 𝕒𝕝𝕘 (str ℐᴮ 𝕋 (str ℐᴮ (□ 𝕋) - ρ) ϱ)) ⟩
        𝕒𝕝𝕘 (str ℐᴮ 𝕋 (str ℐᴮ (□ 𝕋) (⅀₁ (λ{ t ρ ϱ → 𝕣𝕖𝕟 (𝕣𝕖𝕟 t ρ) ϱ}) t) ρ) ϱ)
    ∎ }
  }
  where
  open ≡-Reasoning
  open Renaming


-- Pointed □-coalgebra structure for 𝕋
𝕋ᵇ : Coalg 𝕋
𝕋ᵇ = record { r = 𝕣𝕖𝕟 ; counit = □𝕥𝕣𝕒𝕧-id≈id
            ; comult = λ{ {t = t} → MapEq₂.≈ 𝕣𝕖𝕟-comp t } }

𝕋ᴮ : Coalgₚ 𝕋
𝕋ᴮ = record { ᵇ = 𝕋ᵇ ; η = 𝕧𝕒𝕣 ; r∘η = Renaming.𝕥⟨𝕧⟩ }

-- Algebra and variable maps are coalgebra homomorphisms
𝕒𝕝𝕘ᵇ : Coalg⇒ (Fᵇ 𝕋ᵇ) 𝕋ᵇ 𝕒𝕝𝕘
𝕒𝕝𝕘ᵇ = record { ⟨r⟩ = λ{ {ρ = ρ}{t} → sym Renaming.𝕥⟨𝕒⟩ }}

𝕧𝕒𝕣ᵇ : Coalg⇒ ℐᵇ 𝕋ᵇ 𝕧𝕒𝕣
𝕧𝕒𝕣ᵇ = record { ⟨r⟩ = λ{ {ρ = ρ}{t} → sym Renaming.𝕥⟨𝕧⟩ } }
