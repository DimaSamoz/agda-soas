{-
This second-order term syntax was created from the following second-order syntax description:

syntax CommGroup | CG

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
  (⊕C) a b |> add(a, b) = add(b, a)
-}


module CommGroup.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import CommGroup.Signature

private
  variable
    Γ Δ Π : Ctx
    α : *T
    𝔛 : Familyₛ

-- Inductive term declaration
module CG:Terms (𝔛 : Familyₛ) where

  data CG : Familyₛ where
    var  : ℐ ⇾̣ CG
    mvar : 𝔛 α Π → Sub CG Π Γ → CG α Γ

    ε   : CG * Γ
    _⊕_ : CG * Γ → CG * Γ → CG * Γ
    ⊖_  : CG * Γ → CG * Γ

  infixl 20 _⊕_
  infixr 40 ⊖_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  CGᵃ : MetaAlg CG
  CGᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (unitₒ ⋮ _)     → ε
      (addₒ  ⋮ a , b) → _⊕_ a b
      (negₒ  ⋮ a)     → ⊖_  a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module CGᵃ = MetaAlg CGᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : CG ⇾̣ 𝒜
    𝕊 : Sub CG Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  ε        = 𝑎𝑙𝑔 (unitₒ ⋮ tt)
    𝕤𝕖𝕞 (_⊕_ a b) = 𝑎𝑙𝑔 (addₒ  ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (⊖_  a)   = 𝑎𝑙𝑔 (negₒ  ⋮ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ CGᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ CG α Γ) → 𝕤𝕖𝕞 (CGᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (unitₒ ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (addₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (negₒ  ⋮ _) = refl

      𝕊-tab : (mε : Π ~[ CG ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : CG ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ CGᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : CG α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub CG Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! ε = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_⊕_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (⊖_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
CG:Syn : Syntax
CG:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = CG:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open CG:Terms 𝔛 in record
    { ⊥ = CG ⋉ CGᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax CG:Syn public
open CG:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands CGᵃ public
open import SOAS.Metatheory CG:Syn public
