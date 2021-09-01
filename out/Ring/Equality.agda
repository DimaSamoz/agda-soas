{-
This second-order equational theory was created from the following second-order syntax description:

syntax Ring | R

type
  * : 0-ary

term
  zero : * | 𝟘
  add  : *  *  ->  * | _⊕_ l20
  one  : * | 𝟙
  mult : *  *  ->  * | _⊗_ l30
  neg  : *  ->  * | ⊖_ r50

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
-}

module Ring.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Ring.Signature
open import Ring.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution R:Syn
open import SOAS.Metatheory.SecondOrder.Equality R:Syn

private
  variable
    α β γ τ : *T
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ R) α Γ → (𝔐 ▷ R) α Γ → Set where
  𝟘U⊕ᴸ : ⁅ * ⁆̣             ▹ ∅ ⊢       𝟘 ⊕ 𝔞 ≋ₐ 𝔞
  ⊕A   : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (𝔞 ⊕ 𝔟) ⊕ 𝔠 ≋ₐ 𝔞 ⊕ (𝔟 ⊕ 𝔠)
  ⊕C   : ⁅ * ⁆ ⁅ * ⁆̣       ▹ ∅ ⊢       𝔞 ⊕ 𝔟 ≋ₐ 𝔟 ⊕ 𝔞
  𝟙U⊗ᴸ : ⁅ * ⁆̣             ▹ ∅ ⊢       𝟙 ⊗ 𝔞 ≋ₐ 𝔞
  𝟙U⊗ᴿ : ⁅ * ⁆̣             ▹ ∅ ⊢       𝔞 ⊗ 𝟙 ≋ₐ 𝔞
  ⊗A   : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (𝔞 ⊗ 𝔟) ⊗ 𝔠 ≋ₐ 𝔞 ⊗ (𝔟 ⊗ 𝔠)
  ⊗D⊕ᴸ : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ⊗ (𝔟 ⊕ 𝔠) ≋ₐ (𝔞 ⊗ 𝔟) ⊕ (𝔞 ⊗ 𝔠)
  ⊗D⊕ᴿ : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (𝔞 ⊕ 𝔟) ⊗ 𝔠 ≋ₐ (𝔞 ⊗ 𝔠) ⊕ (𝔟 ⊗ 𝔠)
  𝟘X⊗ᴸ : ⁅ * ⁆̣             ▹ ∅ ⊢       𝟘 ⊗ 𝔞 ≋ₐ 𝟘
  𝟘X⊗ᴿ : ⁅ * ⁆̣             ▹ ∅ ⊢       𝔞 ⊗ 𝟘 ≋ₐ 𝟘
  ⊖N⊕ᴸ : ⁅ * ⁆̣             ▹ ∅ ⊢   (⊖ 𝔞) ⊕ 𝔞 ≋ₐ 𝟘

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning

-- Derived equations
𝟘U⊕ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ⊕ 𝟘 ≋ 𝔞
𝟘U⊕ᴿ = tr (ax ⊕C with《 𝔞 ◃ 𝟘 》) (ax 𝟘U⊕ᴸ with《 𝔞 》)
⊖N⊕ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ⊕ (⊖ 𝔞) ≋ 𝟘
⊖N⊕ᴿ = tr (ax ⊕C with《 𝔞 ◃ (⊖ 𝔞) 》) (ax ⊖N⊕ᴸ with《 𝔞 》)
