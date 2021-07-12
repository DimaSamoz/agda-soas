
open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Metatheory.MetaAlgebra

-- Initial-algebra semantics
module SOAS.Metatheory.Semantics {T : Set}
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ) (⅀:Str : Strength ⅀F)
  (𝔛 : Familyₛ) (open SOAS.Metatheory.MetaAlgebra ⅀F 𝔛)
  (𝕋:Init : Initial 𝕄etaAlgebras)
  where

open import SOAS.Context
open import SOAS.Variable
open import SOAS.Construction.Structure as Structure
open import SOAS.Abstract.Hom
import SOAS.Abstract.Coalgebra as →□ ; open →□.Sorted
import SOAS.Abstract.Box as □ ; open □.Sorted

open import SOAS.Metatheory.Algebra ⅀F

open Strength ⅀:Str

private
  variable
    Γ Δ Θ Π : Ctx
    α β : T
    𝒫 𝒬 𝒜 : Familyₛ


open Initial 𝕋:Init

open Object ⊥ public renaming (𝐶 to 𝕋 ; ˢ to 𝕋ᵃ)
open MetaAlg 𝕋ᵃ public renaming (𝑎𝑙𝑔 to 𝕒𝕝𝕘 ; 𝑣𝑎𝑟 to 𝕧𝕒𝕣 ; 𝑚𝑣𝑎𝑟 to 𝕞𝕧𝕒𝕣 ;
                                  𝑚≈₁ to 𝕞≈₁ ; 𝑚≈₂ to 𝕞≈₂)

module Semantics (𝒜ᵃ : MetaAlg 𝒜) where

  open Morphism (! {𝒜 ⋉ 𝒜ᵃ}) public renaming (𝑓 to 𝕤𝕖𝕞 ; ˢ⇒ to 𝕤𝕖𝕞ᵃ⇒)
  open MetaAlg⇒ 𝕤𝕖𝕞ᵃ⇒ public renaming (⟨𝑎𝑙𝑔⟩ to ⟨𝕒⟩ ; ⟨𝑣𝑎𝑟⟩ to ⟨𝕧⟩ ; ⟨𝑚𝑣𝑎𝑟⟩ to ⟨𝕞⟩)
  open MetaAlg 𝒜ᵃ
  module 𝒜 = MetaAlg 𝒜ᵃ

  eq : {g h : 𝕋 ⇾̣ 𝒜} (gᵃ : MetaAlg⇒ 𝕋ᵃ 𝒜ᵃ g) (hᵃ : MetaAlg⇒ 𝕋ᵃ 𝒜ᵃ h) (t : 𝕋 α Γ)
     → g t ≡ h t
  eq {g = g}{h} gᵃ hᵃ t  = !-unique₂ (g ⋉ gᵃ) (h ⋉ hᵃ) {x = t}

  -- The interpretation is equal to any other pointed meta-Λ-algebra
  𝕤𝕖𝕞! : {g : 𝕋 ⇾̣ 𝒜}(gᵃ : MetaAlg⇒ 𝕋ᵃ 𝒜ᵃ g)(t : 𝕋 α Γ) → 𝕤𝕖𝕞 t ≡ g t
  𝕤𝕖𝕞! {g = g} gᵃ t = !-unique (g ⋉ gᵃ) {x = t}

-- Corollaries: every meta-algebra endo-homomorphism is the identity, including 𝕤𝕖𝕞
eq-id : {g : 𝕋 ⇾̣ 𝕋} (gᵃ : MetaAlg⇒ 𝕋ᵃ 𝕋ᵃ g) (t : 𝕋 α Γ) →
        g t ≡ t
eq-id gᵃ t = Semantics.eq 𝕋ᵃ gᵃ (idᵃ 𝕋ᵃ) t

𝕤𝕖𝕞-id : {t : 𝕋 α Γ} → Semantics.𝕤𝕖𝕞 𝕋ᵃ t ≡ t
𝕤𝕖𝕞-id {t = t} = eq-id (Semantics.𝕤𝕖𝕞ᵃ⇒ 𝕋ᵃ) t
