{-
This second-order term syntax was created from the following second-order syntax description:

syntax UTLC | Λ

type
  * : 0-ary

term
  app  : *  *  ->  * | _$_ l20
  lam  : *.*  ->  * | ƛ_ r10

theory
  (ƛβ) b : *.*  a : * |> app (lam (x.b[x]), a) = b[a]
  (ƛη) f : *          |> lam (x.app (f, x))    = f
  (lβ) b : *.*  a : * |> letd (a, x. b) = b[a]
-}


module UTLC.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import UTLC.Signature

private
  variable
    Γ Δ Π : Ctx
    α : *T
    𝔛 : Familyₛ

-- Inductive term declaration
module Λ:Syntax (𝔛 : Familyₛ) where

  data Λ : Familyₛ where
    var  : ℐ ⇾̣ Λ
    mvar : 𝔛 α Π → Sub Λ Π Γ → Λ α Γ

    _$_  : Λ * Γ → Λ * Γ → Λ * Γ
    ƛ_   : Λ * (* ∙ Γ) → Λ * Γ

  infixl 20 _$_
  infixr 10 ƛ_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Λᵃ : MetaAlg Λ
  Λᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (appₒ  ⅋ a , b) → _$_  a b
      (lamₒ  ⅋ a)     → ƛ_   a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Λᵃ = MetaAlg Λᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : Λ ⇾̣ 𝒜
    𝕊 : Sub Λ Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (_$_  a b) = 𝑎𝑙𝑔 (appₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (ƛ_   a)   = 𝑎𝑙𝑔 (lamₒ  ⅋ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Λᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ Λ α Γ) → 𝕤𝕖𝕞 (Λᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (appₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (lamₒ  ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ Λ ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : Λ ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Λᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : Λ α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub Λ Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (_$_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (ƛ_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
Λ:Syn : Syntax
Λ:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = Λ:Syntax.mvar
  ; 𝕋:Init = λ 𝔛 → let open Λ:Syntax 𝔛 in record
    { ⊥ = Λ ⋉ Λᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

open Syntax Λ:Syn public

-- Working area
open Λ:Syntax
open import SOAS.Families.Build
open import SOAS.Syntax.Shorthands Λᵃ

-- Derived operations
letd : Λ 𝔛 * Γ → Λ 𝔛 * (* ∙ Γ) → Λ 𝔛 * Γ
letd a b = (ƛ b) $ a
