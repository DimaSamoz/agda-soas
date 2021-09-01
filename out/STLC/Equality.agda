{-
This second-order equational theory was created from the following second-order syntax description:

syntax STLC | Λ

type
  N   : 0-ary
  _↣_ : 2-ary | r30

term
  app : α ↣ β  α  ->  β | _$_ l20
  lam : α.β  ->  α ↣ β | ƛ_ r10

theory
  (ƛβ) b : α.β  a : α |> app (lam(x.b[x]), a) = b[a]
  (ƛη) f : α ↣ β      |> lam (x. app(f, x))   = f
-}

module STLC.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import STLC.Signature
open import STLC.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution Λ:Syn
open import SOAS.Metatheory.SecondOrder.Equality Λ:Syn

private
  variable
    α β γ τ : ΛT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ Λ) α Γ → (𝔐 ▷ Λ) α Γ → Set where
  ƛβ : ⁅ α ⊩ β ⁆ ⁅ α ⁆̣ ▹ ∅ ⊢ (ƛ 𝔞⟨ x₀ ⟩) $ 𝔟 ≋ₐ 𝔞⟨ 𝔟 ⟩
  ƛη : ⁅ α ↣ β ⁆̣       ▹ ∅ ⊢      ƛ (𝔞 $ x₀) ≋ₐ 𝔞

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
