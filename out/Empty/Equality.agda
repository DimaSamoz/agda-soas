{-
This second-order equational theory was created from the following second-order syntax description:

syntax Empty | E

type
  𝟘 : 0-ary

term
  abort : 𝟘  ->  α

theory
  (𝟘η) e : 𝟘  c : α |> abort(e) = c
-}

module Empty.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Empty.Signature
open import Empty.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution E:Syn
open import SOAS.Metatheory.SecondOrder.Equality E:Syn

private
  variable
    α β γ τ : ET
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ E) α Γ → (𝔐 ▷ E) α Γ → Set where
  𝟘η : ⁅ 𝟘 ⁆ ⁅ α ⁆̣ ▹ ∅ ⊢ abort 𝔞 ≋ₐ 𝔟

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
