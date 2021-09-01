{-
This second-order term syntax was created from the following second-order syntax description:

syntax Monad | M

type
  T : 1-ary

term
  ret  : α  ->  T α
  bind : T α  α.(T β)  ->  T β | _>>=_ r10

theory
  (LU) a : α   b : α.(T β) |> bind (ret(a), x. b[x]) =  b[a]
  (RU) t : T α |> bind (t, x. ret(x)) = t
  (AS) t : T α  b : α.(T β)  c : β.(T γ) |> bind (bind (t, x.b[x]), y.c[y]) = bind (t, x. bind (b[x], y.c[y]))
-}


module Monad.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Monad.Signature

private
  variable
    Γ Δ Π : Ctx
    α β : MT
    𝔛 : Familyₛ

-- Inductive term declaration
module M:Terms (𝔛 : Familyₛ) where

  data M : Familyₛ where
    var  : ℐ ⇾̣ M
    mvar : 𝔛 α Π → Sub M Π Γ → M α Γ

    ret   : M α Γ → M (T α) Γ
    _>>=_ : M (T α) Γ → M (T β) (α ∙ Γ) → M (T β) Γ

  infixr 10 _>>=_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Mᵃ : MetaAlg M
  Mᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (retₒ  ⅋ a)     → ret   a
      (bindₒ ⅋ a , b) → _>>=_ a b
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Mᵃ = MetaAlg Mᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : M ⇾̣ 𝒜
    𝕊 : Sub M Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (ret   a)   = 𝑎𝑙𝑔 (retₒ  ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (_>>=_ a b) = 𝑎𝑙𝑔 (bindₒ ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Mᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ M α Γ) → 𝕤𝕖𝕞 (Mᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (retₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (bindₒ ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ M ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : M ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Mᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : M α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub M Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (ret a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_>>=_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
M:Syn : Syntax
M:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = M:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open M:Terms 𝔛 in record
    { ⊥ = M ⋉ Mᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax M:Syn public
open M:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands Mᵃ public
open import SOAS.Metatheory M:Syn public
