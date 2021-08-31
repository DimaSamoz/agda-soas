{-
This second-order equational theory was created from the following second-order syntax description:

syntax Combinatory | CL

type
  * : 0-ary

term
  app : *  *  ->  * | _$_ l20
  i   : *
  k   : *
  s   : *

theory
  (IA) x     |> app (i, x) = x
  (KA) x y   |> app (app(k, x), y) = x
  (SA) x y z |> app (app (app (s, x), y), z) = app (app(x, z), app(y, z))
-}

module Combinatory.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import Combinatory.Signature
open import Combinatory.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution CL:Syn
open import SOAS.Metatheory.SecondOrder.Equality CL:Syn
open import SOAS.Metatheory

open CL:Syntax
open import SOAS.Syntax.Shorthands CLᵃ

private
  variable
    α β γ τ : *T
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ CL) α Γ → (𝔐 ▷ CL) α Γ → Set where
  IA : ⁅ * ⁆̣             ▹ ∅ ⊢             I $ 𝔞 ≋ₐ 𝔞
  KA : ⁅ * ⁆ ⁅ * ⁆̣       ▹ ∅ ⊢       (K $ 𝔞) $ 𝔟 ≋ₐ 𝔞
  SA : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ ((S $ 𝔞) $ 𝔟) $ 𝔠 ≋ₐ (𝔞 $ 𝔠) $ (𝔟 $ 𝔠)

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
