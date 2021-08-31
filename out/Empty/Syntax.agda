{-
This second-order term syntax was created from the following second-order syntax description:

syntax Empty | E

type
  𝟘 : 0-ary

term
  abort : 𝟘  ->  α

theory
  (𝟘η) e : 𝟘  c : α |> abort(e) = c
-}


module Empty.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Empty.Signature

private
  variable
    Γ Δ Π : Ctx
    α : ET
    𝔛 : Familyₛ

-- Inductive term declaration
module E:Syntax (𝔛 : Familyₛ) where

  data E : Familyₛ where
    var  : ℐ ⇾̣ E
    mvar : 𝔛 α Π → Sub E Π Γ → E α Γ

    abort : E 𝟘 Γ → E α Γ

  

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Eᵃ : MetaAlg E
  Eᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (abortₒ ⅋ a) → abort a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Eᵃ = MetaAlg Eᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : E ⇾̣ 𝒜
    𝕊 : Sub E Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (abort a) = 𝑎𝑙𝑔 (abortₒ ⅋ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Eᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ E α Γ) → 𝕤𝕖𝕞 (Eᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (abortₒ ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ E ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : E ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Eᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : E α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub E Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (abort a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
E:Syn : Syntax
E:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = E:Syntax.mvar
  ; 𝕋:Init = λ 𝔛 → let open E:Syntax 𝔛 in record
    { ⊥ = E ⋉ Eᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

open Syntax E:Syn public

-- Working area
open E:Syntax
open import SOAS.Families.Build
open import SOAS.Syntax.Shorthands Eᵃ

