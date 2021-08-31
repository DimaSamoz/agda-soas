{-
This second-order signature was created from the following second-order syntax description:

syntax Unit | U

type
  𝟙 : 0-ary

term
  unit : 𝟙

theory
  (𝟙η) u : 𝟙 |> u = unit
-}

module Unit.Signature where

open import SOAS.Context

-- Type declaration
data UT : Set where
  𝟙 : UT



open import SOAS.Syntax.Signature UT public
open import SOAS.Syntax.Build UT public

-- Operator symbols
data Uₒ : Set where
  unitₒ : Uₒ

-- Term signature
U:Sig : Signature Uₒ
U:Sig = sig λ
  {  unitₒ  → ⟼₀ 𝟙
  }

open Signature U:Sig public
