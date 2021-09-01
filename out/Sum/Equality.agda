{-
This second-order equational theory was created from the following second-order syntax description:

syntax Sum | S

type
  _⊕_ : 2-ary | l30

term
  inl  : α  ->  α ⊕ β
  inr  : β  ->  α ⊕ β
  case : α ⊕ β  α.γ  β.γ  ->  γ

theory
  (lβ) a : α   f : α.γ  g : β.γ |> case (inl(a), x.f[x], y.g[y])      = f[a]
  (rβ) b : β   f : α.γ  g : β.γ |> case (inr(b), x.f[x], y.g[y])      = g[b]
  (cη) s : α ⊕ β  c : (α ⊕ β).γ |> case (s, x.c[inl(x)], y.c[inr(y)]) = c[s]
-}

module Sum.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Sum.Signature
open import Sum.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution S:Syn
open import SOAS.Metatheory.SecondOrder.Equality S:Syn

private
  variable
    α β γ τ : ST
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ S) α Γ → (𝔐 ▷ S) α Γ → Set where
  lβ : ⁅ α ⁆ ⁅ α ⊩ γ ⁆ ⁅ β ⊩ γ ⁆̣ ▹ ∅ ⊢   case (inl 𝔞) (𝔟⟨ x₀ ⟩) (𝔠⟨ x₀ ⟩) ≋ₐ 𝔟⟨ 𝔞 ⟩
  rβ : ⁅ β ⁆ ⁅ α ⊩ γ ⁆ ⁅ β ⊩ γ ⁆̣ ▹ ∅ ⊢   case (inr 𝔞) (𝔟⟨ x₀ ⟩) (𝔠⟨ x₀ ⟩) ≋ₐ 𝔠⟨ 𝔞 ⟩
  cη : ⁅ α ⊕ β ⁆ ⁅ (α ⊕ β) ⊩ γ ⁆̣ ▹ ∅ ⊢ case 𝔞 (𝔟⟨ inl x₀ ⟩) (𝔟⟨ inr x₀ ⟩) ≋ₐ 𝔟⟨ 𝔞 ⟩

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
