{-
This second-order equational theory was created from the following second-order syntax description:

syntax Prod | P

type
  _⊗_ : 2-ary | l40

term
  pair : α  β  ->  α ⊗ β | ⟨_,_⟩
  fst  : α ⊗ β  ->  α
  snd  : α ⊗ β  ->  β

theory
  (fβ) a : α  b : β |> fst (pair(a, b))      = a
  (sβ) a : α  b : β |> snd (pair(a, b))      = b
  (pη) p : α ⊗ β    |> pair (fst(p), snd(p)) = p
-}

module Prod.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Prod.Signature
open import Prod.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution P:Syn
open import SOAS.Metatheory.SecondOrder.Equality P:Syn

private
  variable
    α β γ τ : PT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ P) α Γ → (𝔐 ▷ P) α Γ → Set where
  fβ : ⁅ α ⁆ ⁅ β ⁆̣ ▹ ∅ ⊢     fst ⟨ 𝔞 , 𝔟 ⟩ ≋ₐ 𝔞
  sβ : ⁅ α ⁆ ⁅ β ⁆̣ ▹ ∅ ⊢     snd ⟨ 𝔞 , 𝔟 ⟩ ≋ₐ 𝔟
  pη : ⁅ α ⊗ β ⁆̣   ▹ ∅ ⊢ ⟨ fst 𝔞 , snd 𝔞 ⟩ ≋ₐ 𝔞

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
