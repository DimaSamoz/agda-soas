{-
This second-order term syntax was created from the following second-order syntax description:

syntax Combinatory | CL

type
  * : 0-ary

term
  app : *  *  ->  * | _$_ l20
  i   : *
  k   : *
  s   : *

theory
  (IA) x     |> app (i, x) = x
  (KA) x y   |> app (app(k, x), y) = x
  (SA) x y z |> app (app (app (s, x), y), z) = app (app(x, z), app(y, z))
-}


module Combinatory.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Combinatory.Signature

private
  variable
    Γ Δ Π : Ctx
    α : *T
    𝔛 : Familyₛ

-- Inductive term declaration
module CL:Syntax (𝔛 : Familyₛ) where

  data CL : Familyₛ where
    var  : ℐ ⇾̣ CL
    mvar : 𝔛 α Π → Sub CL Π Γ → CL α Γ

    _$_ : CL * Γ → CL * Γ → CL * Γ
    I   : CL * Γ
    K   : CL * Γ
    S   : CL * Γ

  infixl 20 _$_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  CLᵃ : MetaAlg CL
  CLᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (appₒ ⅋ a , b) → _$_ a b
      (iₒ   ⅋ _)     → I
      (kₒ   ⅋ _)     → K
      (sₒ   ⅋ _)     → S
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module CLᵃ = MetaAlg CLᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : CL ⇾̣ 𝒜
    𝕊 : Sub CL Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (_$_ a b) = 𝑎𝑙𝑔 (appₒ ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞  I        = 𝑎𝑙𝑔 (iₒ   ⅋ tt)
    𝕤𝕖𝕞  K        = 𝑎𝑙𝑔 (kₒ   ⅋ tt)
    𝕤𝕖𝕞  S        = 𝑎𝑙𝑔 (sₒ   ⅋ tt)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ CLᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ CL α Γ) → 𝕤𝕖𝕞 (CLᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (appₒ ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (iₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (kₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (sₒ   ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ CL ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : CL ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ CLᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : CL α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub CL Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (_$_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! I = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! K = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! S = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
CL:Syn : Syntax
CL:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = CL:Syntax.mvar
  ; 𝕋:Init = λ 𝔛 → let open CL:Syntax 𝔛 in record
    { ⊥ = CL ⋉ CLᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

open Syntax CL:Syn public

-- Working area
open CL:Syntax
open import SOAS.Families.Build
open import SOAS.Syntax.Shorthands CLᵃ

