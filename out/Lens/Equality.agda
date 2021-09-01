{-
This second-order equational theory was created from the following second-order syntax description:

syntax Lens | L

type
  S : 0-ary
  A : 0-ary

term
  get : S  ->  A
  put : S  A  ->  S

theory
  (PG) s : S  a : A   |> get (put (s, a))   = a
  (GP) s : S          |> put (s, get(s))    = s
  (PP) s : S  a b : A |> put (put(s, a), b) = put (s, a)
-}

module Lens.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Lens.Signature
open import Lens.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution L:Syn
open import SOAS.Metatheory.SecondOrder.Equality L:Syn

private
  variable
    α β γ τ : LT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ L) α Γ → (𝔐 ▷ L) α Γ → Set where
  PG : ⁅ S ⁆ ⁅ A ⁆̣       ▹ ∅ ⊢   get (put 𝔞 𝔟) ≋ₐ 𝔟
  GP : ⁅ S ⁆̣             ▹ ∅ ⊢   put 𝔞 (get 𝔞) ≋ₐ 𝔞
  PP : ⁅ S ⁆ ⁅ A ⁆ ⁅ A ⁆̣ ▹ ∅ ⊢ put (put 𝔞 𝔟) 𝔠 ≋ₐ put 𝔞 𝔟

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
