{-
This file was created from the following second-order syntax description:

type *T
  * : 0-ary

term A
  unit : * | ε 
  mult : *  *  ->  * | _+_ l20
-}

module Monoid.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Syntax.Generic.Signature.ArgList
open import SOAS.Metatheory.Syntax

open import Monoid.Signature

private
  variable
    Γ Δ Π : Ctx
    α : *T

-- Inductive term declaration
module A:Syntax (𝔛 : Familyₛ) where

  data A : Familyₛ where
    var  : ℐ ⇾̣ A
    mvar : 𝔛 α Π → Sub A Π Γ → A α Γ

    ε   : A * Γ
    _+_ : A * Γ → A * Γ → A * Γ

  infixl 20 _+_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Aᵃ : MetaAlg A
  Aᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (unitₒ ⅋ _)     → ε
      (multₒ ⅋ a , b) → _+_ a b
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Aᵃ = MetaAlg Aᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : A ⇾̣ 𝒜
    𝕊 : Sub A Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  ε        = 𝑎𝑙𝑔 (unitₒ ⅋ tt)
    𝕤𝕖𝕞 (_+_ a b) = 𝑎𝑙𝑔 (multₒ ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Aᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ A α Γ) → 𝕤𝕖𝕞 (Aᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (unitₒ ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (multₒ ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ A ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : A ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Aᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : A α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub A Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (lookup mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! ε = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_+_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
A:Syn : Syntax
A:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = A:Syntax.mvar
  ; 𝕋:Init = λ 𝔛 → let open A:Syntax 𝔛 in record
    { ⊥ = A ⋉ Aᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

open Syntax A:Syn public

-- Working area
open A:Syntax
open import SOAS.Families.Build
open import SOAS.Syntax.Shorthands Aᵃ
