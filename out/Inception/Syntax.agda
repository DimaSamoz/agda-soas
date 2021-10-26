{-
This second-order term syntax was created from the following second-order syntax description:

syntax Inception | IA

type
  L : 0-ary
  P : 0-ary
  A : 0-ary

term
  rec : L  P  ->  A
  inc : L.A  P.A  ->  A

theory
  (S) p : P   a : P.A |> inc (l. rec (l, p[]), x. a[x]) = a[p[]]
  (E) a : L.A  |> k : L |- inc (l. a[l], x. rec(k, x)) = a[k]
  (W) m : A  a : P.A  |> inc (l. m[], x. a[x]) = m[]
  (A) p : (L,L).A  a : (L,P).A  b : P.A |>         inc (l. inc (k. p[l, k], x. a[l,x]), y. b[y])       = inc (k. inc(l. p[l,k], y.b[y]), x. inc(l. a[l,x], y.b[y]))
-}


module Inception.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Inception.Signature

private
  variable
    Γ Δ Π : Ctx
    α : IAT
    𝔛 : Familyₛ

-- Inductive term declaration
module IA:Terms (𝔛 : Familyₛ) where

  data IA : Familyₛ where
    var  : ℐ ⇾̣ IA
    mvar : 𝔛 α Π → Sub IA Π Γ → IA α Γ

    rec : IA L Γ → IA P Γ → IA A Γ
    inc : IA A (L ∙ Γ) → IA A (P ∙ Γ) → IA A Γ



  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  IAᵃ : MetaAlg IA
  IAᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (recₒ ⋮ a , b) → rec a b
      (incₒ ⋮ a , b) → inc a b
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module IAᵃ = MetaAlg IAᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : IA ⇾̣ 𝒜
    𝕊 : Sub IA Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (rec a b) = 𝑎𝑙𝑔 (recₒ ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (inc a b) = 𝑎𝑙𝑔 (incₒ ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ IAᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ IA α Γ) → 𝕤𝕖𝕞 (IAᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (recₒ ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (incₒ ⋮ _) = refl

      𝕊-tab : (mε : Π ~[ IA ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : IA ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ IAᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : IA α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub IA Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (rec a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (inc a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
IA:Syn : Syntax
IA:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = IA:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open IA:Terms 𝔛 in record
    { ⊥ = IA ⋉ IAᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax IA:Syn public
open IA:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands IAᵃ public
open import SOAS.Metatheory IA:Syn public
