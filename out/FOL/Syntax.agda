{-
This second-order term syntax was created from the following second-order syntax description:

syntax FOL

type
  * : 0-ary
  N : 0-ary

term
  false : * | ⊥
  or    : *  *  ->  * | _∨_ l20
  true  : * | ⊤
  and   : *  *  ->  * | _∧_ l20
  not   : *  ->  * | ¬_ r50
  eq    : N  N  ->  * | _≟_ l20
  all   : N.*  ->  * | ∀′
  ex    : N.*  ->  * | ∃′

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
  (⊤X∨ᴸ) a |> or (true, a) = true
  (⊤X∨ᴿ) a |> or (a, true) = true
  (¬N∧ᴸ) a |> and (not (a), a) = false
  (¬N∧ᴿ) a |> and (a, not (a)) = false
  (DM∧) a b |> not (and (a, b)) = or (not(a), not(b))
  (DM∨) a b |> not (or (a, b)) = and (not(a), not(b))
  (DM∀) p : N.* |> not (all (x. p[x])) = ex  (x. not(p[x]))
  (DM∃) p : N.* |> not (ex  (x. p[x])) = all (x. not(p[x]))
  (∀D∧) p q : N.* |> all (x. and(p[x], q[x])) = and (all(x.p[x]), all(x.q[x]))
  (∃D∨) p q : N.* |> ex (x. or(p[x], q[x])) = or (ex(x.p[x]), ex(x.q[x]))
  (∧P∀ᴸ) p : *  q : N.* |> and (p, all(x.q[x])) = all (x. and(p, q[x]))
  (∧P∃ᴸ) p : *  q : N.* |> and (p, ex (x.q[x])) = ex  (x. and(p, q[x]))
  (∨P∀ᴸ) p : *  q : N.* |> or  (p, all(x.q[x])) = all (x. or (p, q[x]))
  (∨P∃ᴸ) p : *  q : N.* |> or  (p, ex (x.q[x])) = ex  (x. or (p, q[x]))
  (∧P∀ᴿ) p : N.*  q : * |> and (all(x.p[x]), q) = all (x. and(p[x], q))
  (∧P∃ᴿ) p : N.*  q : * |> and (ex (x.p[x]), q) = ex  (x. and(p[x], q))
  (∨P∀ᴿ) p : N.*  q : * |> or  (all(x.p[x]), q) = all (x. or (p[x], q))
  (∨P∃ᴿ) p : N.*  q : * |> or  (ex (x.p[x]), q) = ex  (x. or (p[x], q))
  (∀Eᴸ) p : N.*  n : N |> all (x.p[x]) = and (p[n], all(x.p[x]))
  (∃Eᴸ) p : N.*  n : N |> ex  (x.p[x]) = or  (p[n], ex (x.p[x]))
  (∀Eᴿ) p : N.*  n : N |> all (x.p[x]) = and (all(x.p[x]), p[n])
  (∃Eᴿ) p : N.*  n : N |> ex  (x.p[x]) = or  (ex (x.p[x]), p[n])
  (∃⟹) p : N.*  q : * |> imp (ex (x.p[x]), q) = all (x. imp(p[x], q))
  (∀⟹) p : N.*  q : * |> imp (all(x.p[x]), q) = ex  (x. imp(p[x], q))
-}


module FOL.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import FOL.Signature

private
  variable
    Γ Δ Π : Ctx
    α : FOLT
    𝔛 : Familyₛ

-- Inductive term declaration
module FOL:Syntax (𝔛 : Familyₛ) where

  data FOL : Familyₛ where
    var  : ℐ ⇾̣ FOL
    mvar : 𝔛 α Π → Sub FOL Π Γ → FOL α Γ

    ⊥   : FOL * Γ
    _∨_ : FOL * Γ → FOL * Γ → FOL * Γ
    ⊤   : FOL * Γ
    _∧_ : FOL * Γ → FOL * Γ → FOL * Γ
    ¬_  : FOL * Γ → FOL * Γ
    _≟_ : FOL N Γ → FOL N Γ → FOL * Γ
    ∀′  : FOL * (N ∙ Γ) → FOL * Γ
    ∃′  : FOL * (N ∙ Γ) → FOL * Γ

  infixl 20 _∨_
  infixl 20 _∧_
  infixr 50 ¬_
  infixl 20 _≟_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  FOLᵃ : MetaAlg FOL
  FOLᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (falseₒ ⅋ _)     → ⊥
      (orₒ    ⅋ a , b) → _∨_ a b
      (trueₒ  ⅋ _)     → ⊤
      (andₒ   ⅋ a , b) → _∧_ a b
      (notₒ   ⅋ a)     → ¬_  a
      (eqₒ    ⅋ a , b) → _≟_ a b
      (allₒ   ⅋ a)     → ∀′  a
      (exₒ    ⅋ a)     → ∃′  a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module FOLᵃ = MetaAlg FOLᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : FOL ⇾̣ 𝒜
    𝕊 : Sub FOL Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  ⊥        = 𝑎𝑙𝑔 (falseₒ ⅋ tt)
    𝕤𝕖𝕞 (_∨_ a b) = 𝑎𝑙𝑔 (orₒ    ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞  ⊤        = 𝑎𝑙𝑔 (trueₒ  ⅋ tt)
    𝕤𝕖𝕞 (_∧_ a b) = 𝑎𝑙𝑔 (andₒ   ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (¬_  a)   = 𝑎𝑙𝑔 (notₒ   ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (_≟_ a b) = 𝑎𝑙𝑔 (eqₒ    ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (∀′  a)   = 𝑎𝑙𝑔 (allₒ   ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (∃′  a)   = 𝑎𝑙𝑔 (exₒ    ⅋ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ FOLᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ FOL α Γ) → 𝕤𝕖𝕞 (FOLᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (falseₒ ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (orₒ    ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (trueₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (andₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (notₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (eqₒ    ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (allₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (exₒ    ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ FOL ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : FOL ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ FOLᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : FOL α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub FOL Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
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
      𝕤𝕖𝕞! (_≟_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (∀′ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (∃′ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
FOL:Syn : Syntax
FOL:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = FOL:Syntax.mvar
  ; 𝕋:Init = λ 𝔛 → let open FOL:Syntax 𝔛 in record
    { ⊥ = FOL ⋉ FOLᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

open Syntax FOL:Syn public

-- Working area
open FOL:Syntax
open import SOAS.Families.Build
open import SOAS.Syntax.Shorthands FOLᵃ

-- Derived operations
_⟹_ : FOL 𝔛 * Γ → FOL 𝔛 * Γ → FOL 𝔛 * Γ
p ⟹ q = ¬ p ∨ q
