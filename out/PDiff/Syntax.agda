{-
This second-order term syntax was created from the following second-order syntax description:

syntax PDiff | PD

type
  * : 0-ary

term
  zero  : * | 𝟘
  add   : *  *  ->  * | _⊕_ l20
  one   : * | 𝟙
  mult  : *  *  ->  * | _⊗_ l20
  neg   : *  ->  * | ⊖_ r50
  pdiff : *.*  *  ->  * | ∂_∣_

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
  (∂⊕) a : * |> x : * |- d0 (add (x, a)) = one
  (∂⊗) a : * |> x : * |- d0 (mult(a, x)) = a
  (∂C) f : (*,*).* |> x : *  y : * |- d1 (d0 (f[x,y])) = d0 (d1 (f[x,y]))
  (∂Ch₂) f : (*,*).*  g h : *.* |> x : * |- d0 (f[g[x], h[x]]) = add (mult(pdiff(z. f[z, h[x]], g[x]), d0(g[x])), mult(pdiff(z. f[g[x], z], h[x]), d0(h[x])))
  (∂Ch₁) f g : *.* |> x : * |- d0 (f[g[x]]) = mult (pdiff (z. f[z], g[x]), d0(g[x]))
-}


module PDiff.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import PDiff.Signature

private
  variable
    Γ Δ Π : Ctx
    α : *T
    𝔛 : Familyₛ

-- Inductive term declaration
module PD:Terms (𝔛 : Familyₛ) where

  data PD : Familyₛ where
    var  : ℐ ⇾̣ PD
    mvar : 𝔛 α Π → Sub PD Π Γ → PD α Γ

    𝟘    : PD * Γ
    _⊕_  : PD * Γ → PD * Γ → PD * Γ
    𝟙    : PD * Γ
    _⊗_  : PD * Γ → PD * Γ → PD * Γ
    ⊖_   : PD * Γ → PD * Γ
    ∂_∣_ : PD * (* ∙ Γ) → PD * Γ → PD * Γ

  infixl 20 _⊕_
  infixl 30 _⊗_
  infixr 50 ⊖_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  PDᵃ : MetaAlg PD
  PDᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (zeroₒ  ⅋ _)     → 𝟘
      (addₒ   ⅋ a , b) → _⊕_  a b
      (oneₒ   ⅋ _)     → 𝟙
      (multₒ  ⅋ a , b) → _⊗_  a b
      (negₒ   ⅋ a)     → ⊖_   a
      (pdiffₒ ⅋ a , b) → ∂_∣_ a b
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module PDᵃ = MetaAlg PDᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : PD ⇾̣ 𝒜
    𝕊 : Sub PD Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  𝟘         = 𝑎𝑙𝑔 (zeroₒ  ⅋ tt)
    𝕤𝕖𝕞 (_⊕_  a b) = 𝑎𝑙𝑔 (addₒ   ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞  𝟙         = 𝑎𝑙𝑔 (oneₒ   ⅋ tt)
    𝕤𝕖𝕞 (_⊗_  a b) = 𝑎𝑙𝑔 (multₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (⊖_   a)   = 𝑎𝑙𝑔 (negₒ   ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (∂_∣_ a b) = 𝑎𝑙𝑔 (pdiffₒ ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ PDᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ PD α Γ) → 𝕤𝕖𝕞 (PDᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (zeroₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (addₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (oneₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (multₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (negₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (pdiffₒ ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ PD ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : PD ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ PDᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : PD α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub PD Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
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
      𝕤𝕖𝕞! (∂_∣_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
PD:Syn : Syntax
PD:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = PD:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open PD:Terms 𝔛 in record
    { ⊥ = PD ⋉ PDᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax PD:Syn public
open PD:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands PDᵃ public
open import SOAS.Metatheory PD:Syn public

-- Derived operations
∂₀_ : {𝔛 : Familyₛ} → PD 𝔛 * (* ∙ Γ) → PD 𝔛 * (* ∙ Γ)
∂₀_ {𝔛 = 𝔛} e = ∂ Theory.𝕨𝕜 𝔛 e ∣ x₀
∂₁_ : {𝔛 : Familyₛ} → PD 𝔛 * (* ∙ * ∙ Γ) → PD 𝔛 * (* ∙ * ∙ Γ)
∂₁_ {𝔛 = 𝔛} e = ∂ Theory.𝕨𝕜 𝔛 e ∣ x₁
infix 10 ∂₀_ ∂₁_
