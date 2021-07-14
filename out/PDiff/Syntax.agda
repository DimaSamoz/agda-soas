{-
This file was created from the following second-order syntax description:

type *T
  * : 0-ary

term PD
  add   : *  *  ->  * | _+_ r20
  mult  : *  *  ->  * | _×_ r40
  zero  : * | 𝟘
  one   : * | 𝟙
  neg   : *  ->  * | –_ r50
  pdiff : *.*  *  ->  * | ∂_∣_
-}

module PDiff.Syntax where

open import SOAS.Common hiding (_×_)
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import PDiff.Signature

private
  variable
    Γ Δ Π : Ctx
    α : *T

-- Inductive term declaration
module PD:Syntax (𝔛 : Familyₛ) where

  data PD : Familyₛ where
    var  : ℐ ⇾̣ PD
    mvar : 𝔛 α Π → Sub PD Π Γ → PD α Γ

    _+_  : PD * Γ → PD * Γ → PD * Γ
    _×_  : PD * Γ → PD * Γ → PD * Γ
    𝟘    : PD * Γ
    𝟙    : PD * Γ
    –_   : PD * Γ → PD * Γ
    ∂_∣_ : PD * (* ∙ Γ) → PD * Γ → PD * Γ

  infixr 20 _+_
  infixr 40 _×_
  infixr 50 –_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  PDᵃ : MetaAlg PD
  PDᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (addₒ   ⅋ a , b) → _+_  a b
      (multₒ  ⅋ a , b) → _×_  a b
      (zeroₒ  ⅋ _)     → 𝟘
      (oneₒ   ⅋ _)     → 𝟙
      (negₒ   ⅋ a)     → –_   a
      (pdiffₒ ⅋ a , b) → ∂_∣_ a b
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module PDᵃ = MetaAlg PDᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : PD ⇾̣ 𝒜
    𝕊 : Sub PD Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (_+_  a b) = 𝑎𝑙𝑔 (addₒ   ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (_×_  a b) = 𝑎𝑙𝑔 (multₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞  𝟘         = 𝑎𝑙𝑔 (zeroₒ  ⅋ tt)
    𝕤𝕖𝕞  𝟙         = 𝑎𝑙𝑔 (oneₒ   ⅋ tt)
    𝕤𝕖𝕞 (–_   a)   = 𝑎𝑙𝑔 (negₒ   ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (∂_∣_ a b) = 𝑎𝑙𝑔 (pdiffₒ ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ PDᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ PD α Γ) → 𝕤𝕖𝕞 (PDᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (addₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (multₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (zeroₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (oneₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (negₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (pdiffₒ ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ PD ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : PD ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ PDᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : PD α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub PD Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (_+_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_×_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! 𝟘 = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! 𝟙 = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (–_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (∂_∣_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
PD:Syn : Syntax
PD:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = PD:Syntax.mvar
  ; 𝕋:Init = λ 𝔛 → let open PD:Syntax 𝔛 in record
    { ⊥ = PD ⋉ PDᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

open Syntax PD:Syn public

-- Working area
open PD:Syntax
open import SOAS.Families.Build
open import SOAS.Syntax.Shorthands PDᵃ
open import SOAS.Metatheory PD:Syn

∂₀_ : {𝔛 : Familyₛ} → PD 𝔛 * (* ∙ Γ) → PD 𝔛 * (* ∙ Γ)
∂₀_ {𝔛 = 𝔛} e = ∂ Theory.𝕨𝕜 𝔛 e ∣ x₀
∂₁_ : {𝔛 : Familyₛ} → PD 𝔛 * (* ∙ * ∙ Γ) → PD 𝔛 * (* ∙ * ∙ Γ)
∂₁_ {𝔛 = 𝔛} e = ∂ Theory.𝕨𝕜 𝔛 e ∣ x₁
