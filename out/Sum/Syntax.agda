{-
This second-order term syntax was created from the following second-order syntax description:

syntax Sum | S

type
  _⊕_ : 2-ary | l30

term
  inl  : α  ->  α ⊕ β
  inr  : β  ->  α ⊕ β
  case : α ⊕ β  α.γ  β.γ  ->  γ

theory
  (lβ) a : α   f : α.γ  g : β.γ |> case (inl(a), x.f[x], y.g[y])      = f[a]
  (rβ) b : β   f : α.γ  g : β.γ |> case (inr(b), x.f[x], y.g[y])      = g[b]
  (cη) s : α ⊕ β  c : (α ⊕ β).γ |> case (s, x.c[inl(x)], y.c[inr(y)]) = c[s]
-}


module Sum.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Sum.Signature

private
  variable
    Γ Δ Π : Ctx
    α β γ : ST
    𝔛 : Familyₛ

-- Inductive term declaration
module S:Syntax (𝔛 : Familyₛ) where

  data S : Familyₛ where
    var  : ℐ ⇾̣ S
    mvar : 𝔛 α Π → Sub S Π Γ → S α Γ

    inl  : S α Γ → S (α ⊕ β) Γ
    inr  : S β Γ → S (α ⊕ β) Γ
    case : S (α ⊕ β) Γ → S γ (α ∙ Γ) → S γ (β ∙ Γ) → S γ Γ

  

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Sᵃ : MetaAlg S
  Sᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (inlₒ  ⅋ a)         → inl  a
      (inrₒ  ⅋ a)         → inr  a
      (caseₒ ⅋ a , b , c) → case a b c
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

    𝕤𝕖𝕞 (inl  a)     = 𝑎𝑙𝑔 (inlₒ  ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (inr  a)     = 𝑎𝑙𝑔 (inrₒ  ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (case a b c) = 𝑎𝑙𝑔 (caseₒ ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b , 𝕤𝕖𝕞 c)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Sᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ S α Γ) → 𝕤𝕖𝕞 (Sᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (inlₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (inrₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (caseₒ ⅋ _) = refl

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

      𝕤𝕖𝕞! (inl a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (inr a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (case a b c) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b | 𝕤𝕖𝕞! c = sym ⟨𝑎𝑙𝑔⟩


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

