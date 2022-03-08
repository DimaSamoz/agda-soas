
open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Metatheory.SynAlgebra

-- Coalgebraic traversal maps
module SOAS.Metatheory.Coalgebraic {T : Set}
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ) (⅀:Str : Strength ⅀F)
  (𝔛 : Familyₛ) (open SOAS.Metatheory.SynAlgebra ⅀F 𝔛)
  (𝕋:Init : Initial 𝕊ynAlgebras)
  where

open import SOAS.Context
open import SOAS.Variable
open import SOAS.Abstract.Hom
import SOAS.Abstract.Coalgebra as →□ ; open →□.Sorted
import SOAS.Abstract.Box as □ ; open □.Sorted

open import SOAS.Coalgebraic.Map

open import SOAS.Metatheory.Algebra {T} ⅀F
open import SOAS.Metatheory.Semantics ⅀F ⅀:Str 𝔛 𝕋:Init
open import SOAS.Metatheory.Traversal ⅀F ⅀:Str 𝔛 𝕋:Init
open import SOAS.Metatheory.Renaming ⅀F ⅀:Str 𝔛 𝕋:Init

open Strength ⅀:Str

-- Relationship of traversal and interpretation, assuming 𝒜 has compatible renaming structure
module _ {𝒜 : Familyₛ}(𝒜ᵇ : Coalg 𝒜)(𝒜ᵃ : SynAlg 𝒜)
         (open Semantics 𝒜ᵃ)(open Coalg 𝒜ᵇ)
         (rᵃ⇒ : SynAlg⇒ 𝒜ᵃ (□ᵃ 𝒜ᵃ) r) where

  open SynAlg 𝒜ᵃ
  open SynAlg⇒ rᵃ⇒

  𝒜ᴮ : Coalgₚ 𝒜
  𝒜ᴮ = record { ᵇ = 𝒜ᵇ ; η = 𝑣𝑎𝑟 ; r∘η = cong (λ - → - _) ⟨𝑣𝑎𝑟⟩ }

  -- Interpretation and renaming commute
  𝕤𝕖𝕞∘ren : MapEq₁ ℐᴮ 𝑎𝑙𝑔 (λ t ρ → 𝕤𝕖𝕞 (𝕣𝕖𝕟 t ρ))
                          (λ t ρ → r (𝕤𝕖𝕞 t) ρ)
  𝕤𝕖𝕞∘ren = record
    { φ = 𝑣𝑎𝑟
    ; χ = 𝑚𝑣𝑎𝑟
    ; f⟨𝑣⟩ = trans (cong 𝕤𝕖𝕞 Renaming.𝕥⟨𝕧⟩) ⟨𝕧⟩
    ; f⟨𝑚⟩ = trans (cong 𝕤𝕖𝕞 Renaming.𝕥⟨𝕞⟩) ⟨𝕞⟩
    ; f⟨𝑎⟩ = λ{ {σ = σ}{t} → begin
          𝕤𝕖𝕞 (𝕣𝕖𝕟 (𝕒𝕝𝕘 t) σ)
      ≡⟨ cong 𝕤𝕖𝕞 Renaming.𝕥⟨𝕒⟩ ⟩
          𝕤𝕖𝕞 (𝕒𝕝𝕘 (str ℐᴮ 𝕋 (⅀₁ 𝕣𝕖𝕟 t) σ))
      ≡⟨ ⟨𝕒⟩ ⟩
          𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 (str ℐᴮ 𝕋 (⅀₁ 𝕣𝕖𝕟 t) σ))
      ≡˘⟨ cong 𝑎𝑙𝑔 (str-nat₂ 𝕤𝕖𝕞 (⅀₁ 𝕣𝕖𝕟 t) σ) ⟩
          𝑎𝑙𝑔 (str ℐᴮ 𝒜 (⅀.F₁ (λ { h′ ς → 𝕤𝕖𝕞 (h′ ς) }) (⅀₁ 𝕣𝕖𝕟 t)) σ)
      ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str ℐᴮ 𝒜 - σ)) ⟩
          𝑎𝑙𝑔 (str ℐᴮ 𝒜 (⅀₁ (λ{ t ρ → 𝕤𝕖𝕞 (𝕣𝕖𝕟 t ρ)}) t) σ)
      ∎ }
    ; g⟨𝑣⟩ = trans (r≈₁ ⟨𝕧⟩) (cong (λ - → - _) ⟨𝑣𝑎𝑟⟩)
    ; g⟨𝑚⟩ = trans (r≈₁ ⟨𝕞⟩) (cong (λ - → - _) ⟨𝑚𝑣𝑎𝑟⟩)
    ; g⟨𝑎⟩ = λ{ {σ = σ}{t} → begin
          r (𝕤𝕖𝕞 (𝕒𝕝𝕘 t)) σ
      ≡⟨ r≈₁ ⟨𝕒⟩ ⟩
          r (𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)) σ
      ≡⟨ cong (λ - → - σ) ⟨𝑎𝑙𝑔⟩ ⟩
          𝑎𝑙𝑔 (str ℐᴮ 𝒜 (⅀₁ r (⅀₁ 𝕤𝕖𝕞 t)) σ)
      ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str ℐᴮ 𝒜 - σ)) ⟩
          𝑎𝑙𝑔 (str ℐᴮ 𝒜 (⅀₁ (λ{ t ρ → r (𝕤𝕖𝕞 t) ρ}) t) σ)
      ∎ }
    } where open ≡-Reasoning

  -- Interpretation is a pointed □-coalgebra homomorphism
  𝕤𝕖𝕞ᵇ⇒ : Coalg⇒ 𝕋ᵇ 𝒜ᵇ 𝕤𝕖𝕞
  𝕤𝕖𝕞ᵇ⇒ = record { ⟨r⟩ = λ{ {t = t} → MapEq₁.≈ 𝕤𝕖𝕞∘ren t } }

  𝕤𝕖𝕞ᴮ⇒ : Coalgₚ⇒ 𝕋ᴮ 𝒜ᴮ 𝕤𝕖𝕞
  𝕤𝕖𝕞ᴮ⇒ = record { ᵇ⇒ = 𝕤𝕖𝕞ᵇ⇒ ; ⟨η⟩ = ⟨𝕧⟩ }

-- Coalgebraic traversal maps
module Travᶜ {𝒫 𝒜 : Familyₛ}(𝒫ᴮ : Coalgₚ 𝒫)(𝑎𝑙𝑔 : ⅀ 𝒜 ⇾̣ 𝒜)
               (φ : 𝒫 ⇾̣ 𝒜)(χ : 𝔛 ⇾̣ 〖 𝒜 , 𝒜 〗) where
  open Coalgₚ 𝒫ᴮ

  open Traversal 𝒫ᴮ 𝑎𝑙𝑔 φ χ

  -- Traversal is derived from 𝕤𝕖𝕞, so it is also a pointed coalgebra homomorphism
  𝕥𝕣𝕒𝕧ᵇ⇒ : Coalg⇒ 𝕋ᵇ Travᵇ 𝕥𝕣𝕒𝕧
  𝕥𝕣𝕒𝕧ᵇ⇒ = 𝕤𝕖𝕞ᵇ⇒ Travᵇ Travᵃ record
    { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → dext² (λ ρ ς → cong 𝑎𝑙𝑔 (str-dist 𝒜 (jᶜ 𝒫ᴮ) t ρ ς)) }
    ; ⟨𝑣𝑎𝑟⟩ = refl ; ⟨𝑚𝑣𝑎𝑟⟩ = refl }

  𝕥𝕣𝕒𝕧ᴮ⇒ : Coalgₚ⇒ 𝕋ᴮ Travᴮ 𝕥𝕣𝕒𝕧
  𝕥𝕣𝕒𝕧ᴮ⇒  = record { ᵇ⇒ = 𝕥𝕣𝕒𝕧ᵇ⇒ ; ⟨η⟩ = ⟨𝕧⟩ }

  -- Assuming 𝒜 is also a pointed □-coalgebra, traversal also commutes with renaming
  module _ (𝒜ᴮ : Coalgₚ 𝒜)(φᴮ : Coalgₚ⇒ 𝒫ᴮ 𝒜ᴮ φ)
           (𝒜rᵃ : SynAlg⇒ 𝒜ᵃ (□ᵃ 𝒜ᵃ) (Coalgₚ.r 𝒜ᴮ)) where

    private module 𝒜ᴮ = Coalgₚ 𝒜ᴮ
    private module φᴮ = Coalgₚ⇒ φᴮ
    private module 𝒜rᵃ = SynAlg⇒ 𝒜rᵃ

    -- Renaming and interpretation can commute
    r∘𝕥𝕣𝕒𝕧 : MapEq₂ 𝒫ᴮ ℐᴮ 𝑎𝑙𝑔 (λ t σ ϱ → 𝒜ᴮ.r (𝕥𝕣𝕒𝕧 t σ) ϱ)
                              (λ t σ ϱ → 𝕥𝕣𝕒𝕧 t (λ v → r (σ v) ϱ))
    r∘𝕥𝕣𝕒𝕧 = record
      { φ = 𝒜ᴮ.η
      ; ϕ = λ v → 𝒜ᴮ.r (φ v)
      ; χ = χ
      ; f⟨𝑣⟩ = 𝒜ᴮ.r≈₁ 𝕥⟨𝕧⟩
      ; f⟨𝑚⟩ = trans (𝒜ᴮ.r≈₁ 𝕥⟨𝕞⟩) (cong (λ - → - _) 𝒜rᵃ.⟨𝑚𝑣𝑎𝑟⟩)
      ; f⟨𝑎⟩ = λ{ {σ = σ}{ϱ}{t} → begin
            𝒜ᴮ.r (𝕥𝕣𝕒𝕧 (𝕒𝕝𝕘 t) σ) ϱ
        ≡⟨ 𝒜ᴮ.r≈₁ 𝕥⟨𝕒⟩ ⟩
            𝒜ᴮ.r (𝑎𝑙𝑔 (str 𝒫ᴮ 𝒜 (⅀₁ 𝕥𝕣𝕒𝕧 t) σ)) ϱ
        ≡⟨ cong (λ - → - ϱ) 𝒜rᵃ.⟨𝑎𝑙𝑔⟩ ⟩
            𝑎𝑙𝑔 (str ℐᴮ 𝒜 (⅀.F₁ 𝒜ᴮ.r (str 𝒫ᴮ 𝒜 (⅀.F₁ 𝕥𝕣𝕒𝕧 t) σ)) ϱ)
        ≡˘⟨ congr (str-nat₂ 𝒜ᴮ.r (⅀.F₁ 𝕥𝕣𝕒𝕧 t) σ) (λ - → 𝑎𝑙𝑔 (str ℐᴮ 𝒜 - ϱ)) ⟩
            𝑎𝑙𝑔 (str ℐᴮ 𝒜 (str 𝒫ᴮ (□ 𝒜) (⅀.F₁ (λ { h ς → 𝒜ᴮ.r (h ς) }) (⅀.F₁ 𝕥𝕣𝕒𝕧 t)) σ) ϱ)
        ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str ℐᴮ 𝒜 (str 𝒫ᴮ (□ 𝒜) - σ)  ϱ)) ⟩
            𝑎𝑙𝑔 (str ℐᴮ 𝒜 (str 𝒫ᴮ (□ 𝒜) (⅀₁ (λ{ t σ → 𝒜ᴮ.r (𝕥𝕣𝕒𝕧 t σ)}) t) σ)  ϱ)
        ∎ }
      ; g⟨𝑣⟩ = trans 𝕥⟨𝕧⟩ φᴮ.⟨r⟩
      ; g⟨𝑚⟩ = 𝕥⟨𝕞⟩
      ; g⟨𝑎⟩ = λ{ {σ = σ}{ϱ}{t} → begin
            𝕥𝕣𝕒𝕧 (𝕒𝕝𝕘 t) (λ x → r (σ x) ϱ)
        ≡⟨ 𝕥⟨𝕒⟩ ⟩
            𝑎𝑙𝑔 (str 𝒫ᴮ 𝒜 (⅀₁ 𝕥𝕣𝕒𝕧 t) (λ x → r (σ x) ϱ))
        ≡⟨ cong 𝑎𝑙𝑔 (str-dist 𝒜 (rᶜ 𝒫ᴮ) (⅀₁ 𝕥𝕣𝕒𝕧 t) σ ϱ) ⟩
            𝑎𝑙𝑔 (str ℐᴮ 𝒜 (str 𝒫ᴮ (□ 𝒜) (⅀.F₁ (precomp 𝒜 r) (⅀₁ 𝕥𝕣𝕒𝕧 t)) σ) ϱ)
        ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str ℐᴮ 𝒜 (str 𝒫ᴮ (□ 𝒜) - σ) ϱ)) ⟩
            𝑎𝑙𝑔 (str ℐᴮ 𝒜  (str 𝒫ᴮ (□ 𝒜) (⅀₁ (λ{ t σ ϱ → 𝕥𝕣𝕒𝕧 t (λ v → r (σ v) ϱ)}) t) σ) ϱ)
        ∎ }
      } where open ≡-Reasoning

    -- The traversal map 𝕋 ⇾ 〖𝒫, 𝒜〗 is pointed coalgebraic if 𝒜 has coalgebra structure
    𝕥𝕣𝕒𝕧ᶜ : Coalgebraic 𝕋ᴮ 𝒫ᴮ 𝒜ᴮ 𝕥𝕣𝕒𝕧
    𝕥𝕣𝕒𝕧ᶜ = record { r∘f = λ{ {σ = σ}{ϱ}{t = t} → MapEq₂.≈ r∘𝕥𝕣𝕒𝕧 t }
                  ; f∘r = λ{ {ρ = ρ}{ς}{t = t} → cong (λ - → - ς) (Coalg⇒.⟨r⟩ 𝕥𝕣𝕒𝕧ᵇ⇒ {ρ = ρ}{t = t}) }
                  ; f∘η = trans 𝕥⟨𝕧⟩ φᴮ.⟨η⟩ }
