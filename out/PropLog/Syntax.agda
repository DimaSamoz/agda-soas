{-
This second-order term syntax was created from the following second-order syntax description:

syntax PropLog | PR

type
  * : 0-ary

term
  false : * | ⊥
  or    : *  *  ->  * | _∨_ l20
  true  : * | ⊤
  and   : *  *  ->  * | _∧_ l30
  not   : *  ->  * | ¬_ r50

theory
  (⊥U∨ᴸ) a |> or (false, a) = a
  (⊥U∨ᴿ) a |> or (a, false) = a
  (∨A) a b c |> or (or(a, b), c) = or (a, or(b, c))
  (∨C) a b |> or(a, b) = or(b, a)
  (⊤U∧ᴸ) a |> and (true, a) = a
  (⊤U∧ᴿ) a |> and (a, true) = a
  (∧A) a b c |> and (and(a, b), c) = and (a, and(b, c))
  (∧D∨ᴸ) a b c |> and (a, or (b, c)) = or (and(a, b), and(a, c))
  (∧D∨ᴿ) a b c |> and (or (a, b), c) = or (and(a, c), and(b, c))
  (⊥X∧ᴸ) a |> and (false, a) = false
  (⊥X∧ᴿ) a |> and (a, false) = false
  (¬N∨ᴸ) a |> or (not (a), a) = false
  (¬N∨ᴿ) a |> or (a, not (a)) = false
  (∧C) a b |> and(a, b) = and(b, a)
  (∨I) a |> or(a, a) = a
  (∧I) a |> and(a, a) = a
  (¬²) a |> not(not (a)) = a
  (∨D∧ᴸ) a b c |> or (a, and (b, c)) = and (or(a, b), or(a, c))
  (∨D∧ᴿ) a b c |> or (and (a, b), c) = and (or(a, c), or(b, c))
  (∨B∧ᴸ) a b |> or (and (a, b), a) = a
  (∨B∧ᴿ) a b |> or (a, and (a, b)) = a
  (∧B∨ᴸ) a b |> and (or (a, b), a) = a
  (∧B∨ᴿ) a b |> and (a, or (a, b)) = a
  (⊤X∨ᴸ) a |> or (true, a) = true
  (⊤X∨ᴿ) a |> or (a, true) = true
  (¬N∧ᴸ) a |> and (not (a), a) = false
  (¬N∧ᴿ) a |> and (a, not (a)) = false
  (DM∧) a b |> not (and (a, b)) = or  (not(a), not(b))
  (DM∨) a b |> not (or  (a, b)) = and (not(a), not(b))
-}


module PropLog.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import PropLog.Signature

private
  variable
    Γ Δ Π : Ctx
    α : *T
    𝔛 : Familyₛ

-- Inductive term declaration
module PR:Terms (𝔛 : Familyₛ) where

  data PR : Familyₛ where
    var  : ℐ ⇾̣ PR
    mvar : 𝔛 α Π → Sub PR Π Γ → PR α Γ

    ⊥   : PR * Γ
    _∨_ : PR * Γ → PR * Γ → PR * Γ
    ⊤   : PR * Γ
    _∧_ : PR * Γ → PR * Γ → PR * Γ
    ¬_  : PR * Γ → PR * Γ

  infixl 20 _∨_
  infixl 30 _∧_
  infixr 50 ¬_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  PRᵃ : MetaAlg PR
  PRᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (falseₒ ⋮ _)     → ⊥
      (orₒ    ⋮ a , b) → _∨_ a b
      (trueₒ  ⋮ _)     → ⊤
      (andₒ   ⋮ a , b) → _∧_ a b
      (notₒ   ⋮ a)     → ¬_  a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module PRᵃ = MetaAlg PRᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : PR ⇾̣ 𝒜
    𝕊 : Sub PR Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  ⊥        = 𝑎𝑙𝑔 (falseₒ ⋮ tt)
    𝕤𝕖𝕞 (_∨_ a b) = 𝑎𝑙𝑔 (orₒ    ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞  ⊤        = 𝑎𝑙𝑔 (trueₒ  ⋮ tt)
    𝕤𝕖𝕞 (_∧_ a b) = 𝑎𝑙𝑔 (andₒ   ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (¬_  a)   = 𝑎𝑙𝑔 (notₒ   ⋮ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ PRᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ PR α Γ) → 𝕤𝕖𝕞 (PRᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (falseₒ ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (orₒ    ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (trueₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (andₒ   ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (notₒ   ⋮ _) = refl

      𝕊-tab : (mε : Π ~[ PR ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : PR ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ PRᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : PR α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub PR Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! ⊥ = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_∨_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! ⊤ = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_∧_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (¬_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
PR:Syn : Syntax
PR:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = PR:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open PR:Terms 𝔛 in record
    { ⊥ = PR ⋉ PRᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax PR:Syn public
open PR:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands PRᵃ public
open import SOAS.Metatheory PR:Syn public

-- Derived operations
_⟹_ : PR 𝔛 * Γ → PR 𝔛 * Γ → PR 𝔛 * Γ
p ⟹ q = ¬ p ∨ q
