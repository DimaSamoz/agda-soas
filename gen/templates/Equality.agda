{-
This second-order equational theory was created from the following second-order syntax description:

$sig_string
-}

module $syn_name.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import $syn_name.Signature
open import $syn_name.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution ${sig}:Syn
open import SOAS.Metatheory.SecondOrder.Equality ${sig}:Syn

private
  variable
    α β γ τ : $type
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ ${sig}) α Γ → (𝔐 ▷ ${sig}) α Γ → Set where
  $axioms

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning

$derived_eqs
