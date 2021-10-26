{-
This second-order term syntax was created from the following second-order syntax description:

syntax Prod | P

type
  _⊗_ : 2-ary | l40

term
  pair : α  β  ->  α ⊗ β | ⟨_,_⟩
  fst  : α ⊗ β  ->  α
  snd  : α ⊗ β  ->  β

theory
  (fβ) a : α  b : β |> fst (pair(a, b))      = a
  (sβ) a : α  b : β |> snd (pair(a, b))      = b
  (pη) p : α ⊗ β    |> pair (fst(p), snd(p)) = p
-}


module Prod.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Prod.Signature

private
  variable
    Γ Δ Π : Ctx
    α β : PT
    𝔛 : Familyₛ

-- Inductive term declaration
module P:Terms (𝔛 : Familyₛ) where

  data P : Familyₛ where
    var  : ℐ ⇾̣ P
    mvar : 𝔛 α Π → Sub P Π Γ → P α Γ

    ⟨_,_⟩ : P α Γ → P β Γ → P (α ⊗ β) Γ
    fst   : P (α ⊗ β) Γ → P α Γ
    snd   : P (α ⊗ β) Γ → P β Γ



  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Pᵃ : MetaAlg P
  Pᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (pairₒ ⋮ a , b) → ⟨_,_⟩ a b
      (fstₒ  ⋮ a)     → fst   a
      (sndₒ  ⋮ a)     → snd   a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Pᵃ = MetaAlg Pᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : P ⇾̣ 𝒜
    𝕊 : Sub P Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (⟨_,_⟩ a b) = 𝑎𝑙𝑔 (pairₒ ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (fst   a)   = 𝑎𝑙𝑔 (fstₒ  ⋮ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (snd   a)   = 𝑎𝑙𝑔 (sndₒ  ⋮ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Pᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ P α Γ) → 𝕤𝕖𝕞 (Pᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (pairₒ ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (fstₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (sndₒ  ⋮ _) = refl

      𝕊-tab : (mε : Π ~[ P ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : P ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Pᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : P α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub P Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (⟨_,_⟩ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (fst a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (snd a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
P:Syn : Syntax
P:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = P:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open P:Terms 𝔛 in record
    { ⊥ = P ⋉ Pᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax P:Syn public
open P:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands Pᵃ public
open import SOAS.Metatheory P:Syn public
