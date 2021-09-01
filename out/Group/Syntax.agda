{-
This second-order term syntax was created from the following second-order syntax description:

syntax Group | G

type
  * : 0-ary

term
  unit : * | ε
  add  : *  *  ->  * | _⊕_ l20
  neg  : *  ->  * | ⊖_ r40

theory
  (εU⊕ᴸ) a |> add (unit, a) = a
  (εU⊕ᴿ) a |> add (a, unit) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
  (⊖N⊕ᴸ) a |> add (neg (a), a) = unit
  (⊖N⊕ᴿ) a |> add (a, neg (a)) = unit
-}


module Group.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Group.Signature

private
  variable
    Γ Δ Π : Ctx
    α : *T
    𝔛 : Familyₛ

-- Inductive term declaration
module G:Terms (𝔛 : Familyₛ) where

  data G : Familyₛ where
    var  : ℐ ⇾̣ G
    mvar : 𝔛 α Π → Sub G Π Γ → G α Γ

    ε   : G * Γ
    _⊕_ : G * Γ → G * Γ → G * Γ
    ⊖_  : G * Γ → G * Γ

  infixl 20 _⊕_
  infixr 40 ⊖_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Gᵃ : MetaAlg G
  Gᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (unitₒ ⅋ _)     → ε
      (addₒ  ⅋ a , b) → _⊕_ a b
      (negₒ  ⅋ a)     → ⊖_  a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Gᵃ = MetaAlg Gᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : G ⇾̣ 𝒜
    𝕊 : Sub G Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  ε        = 𝑎𝑙𝑔 (unitₒ ⅋ tt)
    𝕤𝕖𝕞 (_⊕_ a b) = 𝑎𝑙𝑔 (addₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (⊖_  a)   = 𝑎𝑙𝑔 (negₒ  ⅋ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Gᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ G α Γ) → 𝕤𝕖𝕞 (Gᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (unitₒ ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (addₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (negₒ  ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ G ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : G ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Gᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : G α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub G Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! ε = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_⊕_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (⊖_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
G:Syn : Syntax
G:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = G:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open G:Terms 𝔛 in record
    { ⊥ = G ⋉ Gᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax G:Syn public
open G:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands Gᵃ public
open import SOAS.Metatheory G:Syn public
