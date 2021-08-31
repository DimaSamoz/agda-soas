{-
This second-order equational theory was created from the following second-order syntax description:

syntax UTLC | Λ

type
  * : 0-ary

term
  app  : *  *  ->  * | _$_ l20
  lam  : *.*  ->  * | ƛ_ r10

theory
  (ƛβ) b : *.*  a : * |> app (lam (x.b[x]), a) = b[a]
  (ƛη) f : *          |> lam (x.app (f, x))    = f
  (lβ) b : *.*  a : * |> letd (a, x. b) = b[a]
-}

module UTLC.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import UTLC.Signature
open import UTLC.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution Λ:Syn
open import SOAS.Metatheory.SecondOrder.Equality Λ:Syn
open import SOAS.Metatheory

open Λ:Syntax
open import SOAS.Syntax.Shorthands Λᵃ

private
  variable
    α β γ τ : *T
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ Λ) α Γ → (𝔐 ▷ Λ) α Γ → Set where
  ƛβ : ⁅ * ⊩ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (ƛ 𝔞⟨ x₀ ⟩) $ 𝔟 ≋ₐ 𝔞⟨ 𝔟 ⟩
  ƛη : ⁅ * ⁆̣           ▹ ∅ ⊢      ƛ (𝔞 $ x₀) ≋ₐ 𝔞

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning

-- Derived equations
lβ : ⁅ * ⊩ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ letd 𝔟 (𝔞⟨ x₀ ⟩) ≋ 𝔞⟨ 𝔟 ⟩
lβ = ax ƛβ with《 𝔞⟨ x₀ ⟩ ◃ 𝔟 》
