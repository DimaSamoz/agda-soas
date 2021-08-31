{-
This second-order equational theory was created from the following second-order syntax description:

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

module Monad.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Monad.Signature
open import Monad.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution M:Syn
open import SOAS.Metatheory.SecondOrder.Equality M:Syn
open import SOAS.Metatheory

open M:Syntax
open import SOAS.Syntax.Shorthands Mᵃ

private
  variable
    α β γ τ : MT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ M) α Γ → (𝔐 ▷ M) α Γ → Set where
  LU : ⁅ α ⁆ ⁅ α ⊩ T β ⁆̣               ▹ ∅ ⊢         (ret 𝔞) >>= 𝔟⟨ x₀ ⟩ ≋ₐ 𝔟⟨ 𝔞 ⟩
  RU : ⁅ T α ⁆̣                         ▹ ∅ ⊢              𝔞 >>= (ret x₀) ≋ₐ 𝔞
  AS : ⁅ T α ⁆ ⁅ α ⊩ T β ⁆ ⁅ β ⊩ T γ ⁆̣ ▹ ∅ ⊢ (𝔞 >>= 𝔟⟨ x₀ ⟩) >>= 𝔠⟨ x₀ ⟩ ≋ₐ 𝔞 >>= (𝔟⟨ x₀ ⟩ >>= 𝔠⟨ x₀ ⟩)

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
