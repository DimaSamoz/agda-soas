{-
This second-order term syntax was created from the following second-order syntax description:

syntax CommRing | CR

type
  * : 0-ary

term
  zero : * | 𝟘 
  add  : *  *  ->  * | _⊕_ l20
  one  : * | 𝟙 
  mult : *  *  ->  * | _⊗_ l30
  neg  : *  ->  * | ⊖_ r50

theory
  (𝟘U⊕ᴸ) a |> add (zero, a) = a
  (𝟘U⊕ᴿ) a |> add (a, zero) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
  (⊕C) a b |> add(a, b) = add(b, a)
  (𝟙U⊗ᴸ) a |> mult (one, a) = a
  (𝟙U⊗ᴿ) a |> mult (a, one) = a
  (⊗A) a b c |> mult (mult(a, b), c) = mult (a, mult(b, c))
  (⊗D⊕ᴸ) a b c |> mult (a, add (b, c)) = add (mult(a, b), mult(a, c))
  (⊗D⊕ᴿ) a b c |> mult (add (a, b), c) = add (mult(a, c), mult(b, c))
  (𝟘X⊗ᴸ) a |> mult (zero, a) = zero
  (𝟘X⊗ᴿ) a |> mult (a, zero) = zero
  (⊖N⊕ᴸ) a |> add (neg (a), a) = zero
  (⊖N⊕ᴿ) a |> add (a, neg (a)) = zero
  (⊗C) a b |> mult(a, b) = mult(b, a)
-}


module CommRing.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import CommRing.Signature

private
  variable
    Γ Δ Π : Ctx
    α : *T
    𝔛 : Familyₛ

-- Inductive term declaration
module CR:Syntax (𝔛 : Familyₛ) where

  data CR : Familyₛ where
    var  : ℐ ⇾̣ CR
    mvar : 𝔛 α Π → Sub CR Π Γ → CR α Γ

    𝟘   : CR * Γ
    _⊕_ : CR * Γ → CR * Γ → CR * Γ
    𝟙   : CR * Γ
    _⊗_ : CR * Γ → CR * Γ → CR * Γ
    ⊖_  : CR * Γ → CR * Γ

  infixl 20 _⊕_
  infixl 30 _⊗_
  infixr 50 ⊖_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  CRᵃ : MetaAlg CR
  CRᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (zeroₒ ⅋ _)     → 𝟘
      (addₒ  ⅋ a , b) → _⊕_ a b
      (oneₒ  ⅋ _)     → 𝟙
      (multₒ ⅋ a , b) → _⊗_ a b
      (negₒ  ⅋ a)     → ⊖_  a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module CRᵃ = MetaAlg CRᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : CR ⇾̣ 𝒜
    𝕊 : Sub CR Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  𝟘        = 𝑎𝑙𝑔 (zeroₒ ⅋ tt)
    𝕤𝕖𝕞 (_⊕_ a b) = 𝑎𝑙𝑔 (addₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞  𝟙        = 𝑎𝑙𝑔 (oneₒ  ⅋ tt)
    𝕤𝕖𝕞 (_⊗_ a b) = 𝑎𝑙𝑔 (multₒ ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (⊖_  a)   = 𝑎𝑙𝑔 (negₒ  ⅋ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ CRᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ CR α Γ) → 𝕤𝕖𝕞 (CRᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (zeroₒ ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (addₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (oneₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (multₒ ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (negₒ  ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ CR ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : CR ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ CRᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : CR α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub CR Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! 𝟘 = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_⊕_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! 𝟙 = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_⊗_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (⊖_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
CR:Syn : Syntax
CR:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = CR:Syntax.mvar
  ; 𝕋:Init = λ 𝔛 → let open CR:Syntax 𝔛 in record
    { ⊥ = CR ⋉ CRᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

open Syntax CR:Syn public

-- Working area
open CR:Syntax
open import SOAS.Families.Build
open import SOAS.Syntax.Shorthands CRᵃ

