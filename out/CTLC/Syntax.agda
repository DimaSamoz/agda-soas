{-
This second-order term syntax was created from the following second-order syntax description:

syntax CTLC | ΛC

type
  N   : 0-ary
  _↣_ : 2-ary | r30
  ¬_  : 1-ary | r30

term
  app    : α ↣ β  α  ->  β | _$_ l20
  lam    : α.β  ->  α ↣ β | ƛ_ r10
  throw  : α  ¬ α  ->  β
  callcc : ¬ α.α  ->  α

theory
  (ƛβ) b : α.β  a : α |> app (lam(x.b[x]), a) = b[a]
  (ƛη) f : α ↣ β      |> lam (x. app(f, x))   = f
-}


module CTLC.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import CTLC.Signature

private
  variable
    Γ Δ Π : Ctx
    α β : ΛCT
    𝔛 : Familyₛ

-- Inductive term declaration
module ΛC:Terms (𝔛 : Familyₛ) where

  data ΛC : Familyₛ where
    var  : ℐ ⇾̣ ΛC
    mvar : 𝔛 α Π → Sub ΛC Π Γ → ΛC α Γ

    _$_    : ΛC (α ↣ β) Γ → ΛC α Γ → ΛC β Γ
    ƛ_     : ΛC β (α ∙ Γ) → ΛC (α ↣ β) Γ
    throw  : ΛC α Γ → ΛC (¬ α) Γ → ΛC β Γ
    callcc : ΛC α ((¬ α) ∙ Γ) → ΛC α Γ

  infixl 20 _$_
  infixr 10 ƛ_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  ΛCᵃ : MetaAlg ΛC
  ΛCᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (appₒ    ⅋ a , b) → _$_    a b
      (lamₒ    ⅋ a)     → ƛ_     a
      (throwₒ  ⅋ a , b) → throw  a b
      (callccₒ ⅋ a)     → callcc a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module ΛCᵃ = MetaAlg ΛCᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : ΛC ⇾̣ 𝒜
    𝕊 : Sub ΛC Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (_$_    a b) = 𝑎𝑙𝑔 (appₒ    ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (ƛ_     a)   = 𝑎𝑙𝑔 (lamₒ    ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (throw  a b) = 𝑎𝑙𝑔 (throwₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (callcc a)   = 𝑎𝑙𝑔 (callccₒ ⅋ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ ΛCᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ ΛC α Γ) → 𝕤𝕖𝕞 (ΛCᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (appₒ    ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (lamₒ    ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (throwₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (callccₒ ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ ΛC ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : ΛC ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ ΛCᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : ΛC α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub ΛC Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (_$_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (ƛ_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (throw a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (callcc a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
ΛC:Syn : Syntax
ΛC:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = ΛC:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open ΛC:Terms 𝔛 in record
    { ⊥ = ΛC ⋉ ΛCᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax ΛC:Syn public
open ΛC:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands ΛCᵃ public
open import SOAS.Metatheory ΛC:Syn public
