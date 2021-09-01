{-
This second-order equational theory was created from the following second-order syntax description:

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

module CTLC.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import CTLC.Signature
open import CTLC.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution ΛC:Syn
open import SOAS.Metatheory.SecondOrder.Equality ΛC:Syn

private
  variable
    α β γ τ : ΛCT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ ΛC) α Γ → (𝔐 ▷ ΛC) α Γ → Set where
  ƛβ : ⁅ α ⊩ β ⁆ ⁅ α ⁆̣ ▹ ∅ ⊢ (ƛ 𝔞⟨ x₀ ⟩) $ 𝔟 ≋ₐ 𝔞⟨ 𝔟 ⟩
  ƛη : ⁅ α ↣ β ⁆̣       ▹ ∅ ⊢      ƛ (𝔞 $ x₀) ≋ₐ 𝔞

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
