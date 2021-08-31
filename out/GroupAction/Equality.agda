{-
This second-order equational theory was created from the following second-order syntax description:

syntax GroupAction | GA

type
  * : 0-ary
  X : 0-ary

term
  unit : * | ε
  add  : *  *  ->  * | _⊕_ l20
  neg  : *  ->  * | ⊖_ r40
  act  : *  X  ->  X | _⊙_ r30

theory
  (εU⊕ᴸ) a |> add (unit, a) = a
  (εU⊕ᴿ) a |> add (a, unit) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
  (⊖N⊕ᴸ) a |> add (neg (a), a) = unit
  (⊖N⊕ᴿ) a |> add (a, neg (a)) = unit
  (εU⊙)      x : X |> act (unit,      x) = x
  (⊕A⊙) g h  x : X |> act (add(g, h), x) = act (g, act(h, x))
-}

module GroupAction.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import GroupAction.Signature
open import GroupAction.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution GA:Syn
open import SOAS.Metatheory.SecondOrder.Equality GA:Syn
open import SOAS.Metatheory

open GA:Syntax
open import SOAS.Syntax.Shorthands GAᵃ

private
  variable
    α β γ τ : GAT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ GA) α Γ → (𝔐 ▷ GA) α Γ → Set where
  εU⊕ᴸ : ⁅ * ⁆̣             ▹ ∅ ⊢       ε ⊕ 𝔞 ≋ₐ 𝔞
  εU⊕ᴿ : ⁅ * ⁆̣             ▹ ∅ ⊢       𝔞 ⊕ ε ≋ₐ 𝔞
  ⊕A   : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (𝔞 ⊕ 𝔟) ⊕ 𝔠 ≋ₐ 𝔞 ⊕ (𝔟 ⊕ 𝔠)
  ⊖N⊕ᴸ : ⁅ * ⁆̣             ▹ ∅ ⊢   (⊖ 𝔞) ⊕ 𝔞 ≋ₐ ε
  ⊖N⊕ᴿ : ⁅ * ⁆̣             ▹ ∅ ⊢   𝔞 ⊕ (⊖ 𝔞) ≋ₐ ε
  εU⊙  : ⁅ X ⁆̣             ▹ ∅ ⊢       ε ⊙ 𝔞 ≋ₐ 𝔞
  ⊕A⊙  : ⁅ * ⁆ ⁅ * ⁆ ⁅ X ⁆̣ ▹ ∅ ⊢ (𝔞 ⊕ 𝔟) ⊙ 𝔠 ≋ₐ 𝔞 ⊙ (𝔟 ⊙ 𝔠)

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
