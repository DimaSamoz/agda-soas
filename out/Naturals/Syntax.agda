{-
This second-order term syntax was created from the following second-order syntax description:

syntax Naturals | Nat

type
  N : 0-ary

term
  ze   : N
  su   : N  ->  N
  nrec : N  α  (α,N).α  ->  α

theory
  (zeβ) z : α   s : (α,N).α        |> nrec (ze,       z, r m. s[r,m]) = z
  (suβ) z : α   s : (α,N).α  n : N |> nrec (su (n), z, r m. s[r,m]) = s[nrec (n, z, r m. s[r,m]), n]
-}


module Naturals.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Naturals.Signature

private
  variable
    Γ Δ Π : Ctx
    α : NatT
    𝔛 : Familyₛ

-- Inductive term declaration
module Nat:Terms (𝔛 : Familyₛ) where

  data Nat : Familyₛ where
    var  : ℐ ⇾̣ Nat
    mvar : 𝔛 α Π → Sub Nat Π Γ → Nat α Γ

    ze   : Nat N Γ
    su   : Nat N Γ → Nat N Γ
    nrec : Nat N Γ → Nat α Γ → Nat α (α ∙ N ∙ Γ) → Nat α Γ



  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Natᵃ : MetaAlg Nat
  Natᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (zeₒ   ⅋ _)         → ze
      (suₒ   ⅋ a)         → su   a
      (nrecₒ ⅋ a , b , c) → nrec a b c
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Natᵃ = MetaAlg Natᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : Nat ⇾̣ 𝒜
    𝕊 : Sub Nat Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  ze          = 𝑎𝑙𝑔 (zeₒ   ⅋ tt)
    𝕤𝕖𝕞 (su   a)     = 𝑎𝑙𝑔 (suₒ   ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (nrec a b c) = 𝑎𝑙𝑔 (nrecₒ ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b , 𝕤𝕖𝕞 c)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Natᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ Nat α Γ) → 𝕤𝕖𝕞 (Natᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (zeₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (suₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (nrecₒ ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ Nat ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : Nat ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Natᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : Nat α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub Nat Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! ze = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (su a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (nrec a b c) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b | 𝕤𝕖𝕞! c = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
Nat:Syn : Syntax
Nat:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = Nat:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open Nat:Terms 𝔛 in record
    { ⊥ = Nat ⋉ Natᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax Nat:Syn public
open Nat:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands Natᵃ public
open import SOAS.Metatheory Nat:Syn public
