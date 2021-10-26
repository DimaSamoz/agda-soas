{-
This second-order term syntax was created from the following second-order syntax description:

syntax Unit | U

type
  𝟙 : 0-ary

term
  unit : 𝟙

theory
  (𝟙η) u : 𝟙 |> u = unit
-}


module Unit.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Unit.Signature

private
  variable
    Γ Δ Π : Ctx
    α : UT
    𝔛 : Familyₛ

-- Inductive term declaration
module U:Terms (𝔛 : Familyₛ) where

  data U : Familyₛ where
    var  : ℐ ⇾̣ U
    mvar : 𝔛 α Π → Sub U Π Γ → U α Γ

    unit : U 𝟙 Γ



  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Uᵃ : MetaAlg U
  Uᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (unitₒ ⋮ _) → unit
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Uᵃ = MetaAlg Uᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : U ⇾̣ 𝒜
    𝕊 : Sub U Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  unit  = 𝑎𝑙𝑔 (unitₒ ⋮ tt)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Uᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ U α Γ) → 𝕤𝕖𝕞 (Uᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (unitₒ ⋮ _) = refl

      𝕊-tab : (mε : Π ~[ U ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : U ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Uᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : U α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub U Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! unit = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
U:Syn : Syntax
U:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = U:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open U:Terms 𝔛 in record
    { ⊥ = U ⋉ Uᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax U:Syn public
open U:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands Uᵃ public
open import SOAS.Metatheory U:Syn public
