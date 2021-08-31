{-
This second-order equational theory was created from the following second-order syntax description:

syntax Sub | S

type
  L : 0-ary
  T : 0-ary

term
  vr : L  ->  T
  sb : L.T  T  ->  T

theory
  (C) x y : T |> sb (a. x[], y[]) = x[]
  (L) x : T |> sb (a. vr(a), x[]) = x[]
  (R) a : L  x : L.T |> sb (b. x[b], vr(a[])) = x[a[]]
  (A) x : (L,L).T  y : L.T  z : T |> sb (a. sb (b. x[a,b], y[a]), z[]) = sb (b. sb (a. x[a, b], z[]), sb (a. y[a], z[]))
-}

module Sub.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Sub.Signature
open import Sub.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution S:Syn
open import SOAS.Metatheory.SecondOrder.Equality S:Syn
open import SOAS.Metatheory

open S:Syntax
open import SOAS.Syntax.Shorthands Sᵃ

private
  variable
    α β γ τ : ST
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ S) α Γ → (𝔐 ▷ S) α Γ → Set where
  C : ⁅ T ⁆ ⁅ T ⁆̣     ▹ ∅ ⊢              sb 𝔞 𝔟 ≋ₐ 𝔞
  L : ⁅ T ⁆̣           ▹ ∅ ⊢        sb (vr x₀) 𝔞 ≋ₐ 𝔞
  R : ⁅ L ⁆ ⁅ L ⊩ T ⁆̣ ▹ ∅ ⊢ sb (𝔟⟨ x₀ ⟩) (vr 𝔞) ≋ₐ 𝔟⟨ 𝔞 ⟩
  A : ⁅ L · L ⊩ T ⁆ ⁅ L ⊩ T ⁆ ⁅ T ⁆̣ ▹ ∅
    ⊢  sb (sb (𝔞⟨ x₁ ◂ x₀ ⟩) (𝔟⟨ x₀ ⟩)) 𝔠 
    ≋ₐ sb (sb (𝔞⟨ x₀ ◂ x₁ ⟩) 𝔠) (sb (𝔟⟨ x₀ ⟩) 𝔠)

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
