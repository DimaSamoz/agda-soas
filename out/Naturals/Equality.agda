{-
This second-order equational theory was created from the following second-order syntax description:

syntax Naturals | Nat

type
  N : 0-ary

term
  ze   : N
  su   : N  ->  N
  nrec : N  α  (α,N).α  ->  α

theory
  (zeβ) z : α   s : (α,N).α        |> nrec (ze,       z, r m. s[r,m]) = z
  (suβ) z : α   s : (α,N).α  n : N |> nrec (su (n), z, r m. s[r,m]) = s[nrec (n, z, r m. s[r,m]), n]
-}

module Naturals.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Naturals.Signature
open import Naturals.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution Nat:Syn
open import SOAS.Metatheory.SecondOrder.Equality Nat:Syn
open import SOAS.Metatheory

open Nat:Syntax
open import SOAS.Syntax.Shorthands Natᵃ

private
  variable
    α β γ τ : NatT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ Nat) α Γ → (𝔐 ▷ Nat) α Γ → Set where
  zeβ : ⁅ α ⁆ ⁅ α · N ⊩ α ⁆̣       ▹ ∅ ⊢     nrec ze 𝔞 (𝔟⟨ x₀ ◂ x₁ ⟩) ≋ₐ 𝔞
  suβ : ⁅ α ⁆ ⁅ α · N ⊩ α ⁆ ⁅ N ⁆̣ ▹ ∅ ⊢ nrec (su 𝔠) 𝔞 (𝔟⟨ x₀ ◂ x₁ ⟩) ≋ₐ 𝔟⟨ (nrec 𝔠 𝔞 (𝔟⟨ x₀ ◂ x₁ ⟩)) ◂ 𝔠 ⟩

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning

