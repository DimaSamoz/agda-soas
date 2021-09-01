{-
This second-order equational theory was created from the following second-order syntax description:

syntax Monoid | M

type
  * : 0-ary

term
  unit : * | ε
  add  : *  *  ->  * | _⊕_ l20

theory
  (εU⊕ᴸ) a |> add (unit, a) = a
  (εU⊕ᴿ) a |> add (a, unit) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
-}

module Monoid.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Monoid.Signature
open import Monoid.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution M:Syn
open import SOAS.Metatheory.SecondOrder.Equality M:Syn

private
  variable
    α β γ τ : *T
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ M) α Γ → (𝔐 ▷ M) α Γ → Set where
  εU⊕ᴸ : ⁅ * ⁆̣             ▹ ∅ ⊢       ε ⊕ 𝔞 ≋ₐ 𝔞
  εU⊕ᴿ : ⁅ * ⁆̣             ▹ ∅ ⊢       𝔞 ⊕ ε ≋ₐ 𝔞
  ⊕A   : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (𝔞 ⊕ 𝔟) ⊕ 𝔠 ≋ₐ 𝔞 ⊕ (𝔟 ⊕ 𝔠)

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
