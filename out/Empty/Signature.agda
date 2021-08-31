{-
This second-order signature was created from the following second-order syntax description:

syntax Empty | E

type
  𝟘 : 0-ary

term
  abort : 𝟘  ->  α

theory
  (𝟘η) e : 𝟘  c : α |> abort(e) = c
-}

module Empty.Signature where

open import SOAS.Context

-- Type declaration
data ET : Set where
  𝟘 : ET



open import SOAS.Syntax.Signature ET public
open import SOAS.Syntax.Build ET public

-- Operator symbols
data Eₒ : Set where
  abortₒ : {α : ET} → Eₒ

-- Term signature
E:Sig : Signature Eₒ
E:Sig = sig λ
  { (abortₒ {α}) → (⊢₀ 𝟘) ⟼₁ α
  }

open Signature E:Sig public
