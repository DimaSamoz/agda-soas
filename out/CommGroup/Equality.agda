{-
This second-order equational theory was created from the following second-order syntax description:

syntax CommGroup | CG

type
  * : 0-ary

term
  unit : * | ε
  add  : *  *  ->  * | _⊕_ l20
  neg  : *  ->  * | ⊖_ r40

theory
  (εU⊕ᴸ) a |> add (unit, a) = a
  (εU⊕ᴿ) a |> add (a, unit) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
  (⊖N⊕ᴸ) a |> add (neg (a), a) = unit
  (⊖N⊕ᴿ) a |> add (a, neg (a)) = unit
  (⊕C) a b |> add(a, b) = add(b, a)
-}

module CommGroup.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import CommGroup.Signature
open import CommGroup.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution CG:Syn
open import SOAS.Metatheory.SecondOrder.Equality CG:Syn

private
  variable
    α β γ τ : *T
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ CG) α Γ → (𝔐 ▷ CG) α Γ → Set where
  εU⊕ᴸ : ⁅ * ⁆̣             ▹ ∅ ⊢       ε ⊕ 𝔞 ≋ₐ 𝔞
  ⊕A   : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (𝔞 ⊕ 𝔟) ⊕ 𝔠 ≋ₐ 𝔞 ⊕ (𝔟 ⊕ 𝔠)
  ⊖N⊕ᴸ : ⁅ * ⁆̣             ▹ ∅ ⊢   (⊖ 𝔞) ⊕ 𝔞 ≋ₐ ε
  ⊕C   : ⁅ * ⁆ ⁅ * ⁆̣       ▹ ∅ ⊢       𝔞 ⊕ 𝔟 ≋ₐ 𝔟 ⊕ 𝔞

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning

-- Derived equations
εU⊕ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ⊕ ε ≋ 𝔞
εU⊕ᴿ = tr (ax ⊕C with《 𝔞 ◃ ε 》) (ax εU⊕ᴸ with《 𝔞 》)
⊖N⊕ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ⊕ (⊖ 𝔞) ≋ ε
⊖N⊕ᴿ = tr (ax ⊕C with《 𝔞 ◃ (⊖ 𝔞) 》) (ax ⊖N⊕ᴸ with《 𝔞 》)
