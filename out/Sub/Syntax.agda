{-
This second-order term syntax was created from the following second-order syntax description:

syntax Sub | S

type
  L : 0-ary
  T : 0-ary

term
  vr : L  ->  T
  sb : L.T  T  ->  T

theory
  (C) x y : T |> sb (a. x[], y[]) = x[]
  (L) x : T |> sb (a. vr(a), x[]) = x[]
  (R) a : L  x : L.T |> sb (b. x[b], vr(a[])) = x[a[]]
  (A) x : (L,L).T  y : L.T  z : T |> sb (a. sb (b. x[a,b], y[a]), z[]) = sb (b. sb (a. x[a, b], z[]), sb (a. y[a], z[]))
-}


module Sub.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Sub.Signature

private
  variable
    Γ Δ Π : Ctx
    α : ST
    𝔛 : Familyₛ

-- Inductive term declaration
module S:Syntax (𝔛 : Familyₛ) where

  data S : Familyₛ where
    var  : ℐ ⇾̣ S
    mvar : 𝔛 α Π → Sub S Π Γ → S α Γ

    vr : S L Γ → S T Γ
    sb : S T (L ∙ Γ) → S T Γ → S T Γ

  

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Sᵃ : MetaAlg S
  Sᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (vrₒ ⅋ a)     → vr a
      (sbₒ ⅋ a , b) → sb a b
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Sᵃ = MetaAlg Sᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : S ⇾̣ 𝒜
    𝕊 : Sub S Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (vr a)   = 𝑎𝑙𝑔 (vrₒ ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (sb a b) = 𝑎𝑙𝑔 (sbₒ ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Sᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ S α Γ) → 𝕤𝕖𝕞 (Sᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (vrₒ ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (sbₒ ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ S ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : S ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Sᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : S α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub S Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (vr a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (sb a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
S:Syn : Syntax
S:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = S:Syntax.mvar
  ; 𝕋:Init = λ 𝔛 → let open S:Syntax 𝔛 in record
    { ⊥ = S ⋉ Sᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

open Syntax S:Syn public

-- Working area
open S:Syntax
open import SOAS.Families.Build
open import SOAS.Syntax.Shorthands Sᵃ

