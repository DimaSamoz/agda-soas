{-
This second-order equational theory was created from the following second-order syntax description:

syntax Inception | IA

type
  L : 0-ary
  P : 0-ary
  A : 0-ary

term
  rec : L  P  ->  A
  inc : L.A  P.A  ->  A

theory
  (S) p : P   a : P.A |> inc (l. rec (l, p[]), x. a[x]) = a[p[]]
  (E) a : L.A  |> k : L |- inc (l. a[l], x. rec(k, x)) = a[k]
  (W) m : A  a : P.A  |> inc (l. m[], x. a[x]) = m[]
  (A) p : (L,L).A  a : (L,P).A  b : P.A |>         inc (l. inc (k. p[l, k], x. a[l,x]), y. b[y])       = inc (k. inc(l. p[l,k], y.b[y]), x. inc(l. a[l,x], y.b[y]))
-}

module Inception.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Inception.Signature
open import Inception.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution IA:Syn
open import SOAS.Metatheory.SecondOrder.Equality IA:Syn

private
  variable
    α β γ τ : IAT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ IA) α Γ → (𝔐 ▷ IA) α Γ → Set where
  S : ⁅ P ⁆ ⁅ P ⊩ A ⁆̣ ▹   ∅   ⊢  inc (rec x₀ 𝔞) (𝔟⟨ x₀ ⟩) ≋ₐ 𝔟⟨ 𝔞 ⟩
  E : ⁅ L ⊩ A ⁆̣       ▹ ⌊ L ⌋ ⊢ inc (𝔞⟨ x₀ ⟩) (rec x₁ x₀) ≋ₐ 𝔞⟨ x₀ ⟩
  W : ⁅ A ⁆ ⁅ P ⊩ A ⁆̣ ▹   ∅   ⊢           inc 𝔞 (𝔟⟨ x₀ ⟩) ≋ₐ 𝔞
  A : ⁅ L · L ⊩ A ⁆ ⁅ L · P ⊩ A ⁆ ⁅ P ⊩ A ⁆̣ ▹ ∅
    ⊢ inc (inc (𝔞⟨ x₁ ◂ x₀ ⟩) (𝔟⟨ x₁ ◂ x₀ ⟩)) (𝔠⟨ x₀ ⟩)
   ≋ₐ inc (inc (𝔞⟨ x₀ ◂ x₁ ⟩) (𝔠⟨ x₀ ⟩)) (inc (𝔟⟨ x₀ ◂ x₁ ⟩) (𝔠⟨ x₀ ⟩))

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
