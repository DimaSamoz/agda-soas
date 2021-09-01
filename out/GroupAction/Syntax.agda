{-
This second-order term syntax was created from the following second-order syntax description:

syntax GroupAction | GA

type
  * : 0-ary
  X : 0-ary

term
  unit : * | ε
  add  : *  *  ->  * | _⊕_ l20
  neg  : *  ->  * | ⊖_ r40
  act  : *  X  ->  X | _⊙_ r30

theory
  (εU⊕ᴸ) a |> add (unit, a) = a
  (εU⊕ᴿ) a |> add (a, unit) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
  (⊖N⊕ᴸ) a |> add (neg (a), a) = unit
  (⊖N⊕ᴿ) a |> add (a, neg (a)) = unit
  (εU⊙)      x : X |> act (unit,      x) = x
  (⊕A⊙) g h  x : X |> act (add(g, h), x) = act (g, act(h, x))
-}


module GroupAction.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import GroupAction.Signature

private
  variable
    Γ Δ Π : Ctx
    α : GAT
    𝔛 : Familyₛ

-- Inductive term declaration
module GA:Terms (𝔛 : Familyₛ) where

  data GA : Familyₛ where
    var  : ℐ ⇾̣ GA
    mvar : 𝔛 α Π → Sub GA Π Γ → GA α Γ

    ε   : GA * Γ
    _⊕_ : GA * Γ → GA * Γ → GA * Γ
    ⊖_  : GA * Γ → GA * Γ
    _⊙_ : GA * Γ → GA X Γ → GA X Γ

  infixl 20 _⊕_
  infixr 40 ⊖_
  infixr 30 _⊙_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  GAᵃ : MetaAlg GA
  GAᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (unitₒ ⅋ _)     → ε
      (addₒ  ⅋ a , b) → _⊕_ a b
      (negₒ  ⅋ a)     → ⊖_  a
      (actₒ  ⅋ a , b) → _⊙_ a b
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module GAᵃ = MetaAlg GAᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : GA ⇾̣ 𝒜
    𝕊 : Sub GA Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  ε        = 𝑎𝑙𝑔 (unitₒ ⅋ tt)
    𝕤𝕖𝕞 (_⊕_ a b) = 𝑎𝑙𝑔 (addₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (⊖_  a)   = 𝑎𝑙𝑔 (negₒ  ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (_⊙_ a b) = 𝑎𝑙𝑔 (actₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ GAᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ GA α Γ) → 𝕤𝕖𝕞 (GAᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (unitₒ ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (addₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (negₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (actₒ  ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ GA ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : GA ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ GAᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : GA α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub GA Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! ε = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_⊕_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (⊖_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_⊙_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
GA:Syn : Syntax
GA:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = GA:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open GA:Terms 𝔛 in record
    { ⊥ = GA ⋉ GAᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax GA:Syn public
open GA:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands GAᵃ public
open import SOAS.Metatheory GA:Syn public
