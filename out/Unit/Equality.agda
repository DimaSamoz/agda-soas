{-
This second-order equational theory was created from the following second-order syntax description:

syntax Unit | U

type
  𝟙 : 0-ary

term
  unit : 𝟙

theory
  (𝟙η) u : 𝟙 |> u = unit
-}

module Unit.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Unit.Signature
open import Unit.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution U:Syn
open import SOAS.Metatheory.SecondOrder.Equality U:Syn

private
  variable
    α β γ τ : UT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ U) α Γ → (𝔐 ▷ U) α Γ → Set where
  𝟙η : ⁅ 𝟙 ⁆̣ ▹ ∅ ⊢ 𝔞 ≋ₐ unit

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
