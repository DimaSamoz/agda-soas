{-
This second-order signature was created from the following second-order syntax description:

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

module Lens.Signature where

open import SOAS.Context

-- Type declaration
data LT : Set where
  S : LT
  A : LT



open import SOAS.Syntax.Signature LT public
open import SOAS.Syntax.Build LT public

-- Operator symbols
data Lₒ : Set where
  getₒ putₒ : Lₒ

-- Term signature
L:Sig : Signature Lₒ
L:Sig = sig λ
  {  getₒ  → (⊢₀ S) ⟼₁ A
  ;  putₒ  → (⊢₀ S) , (⊢₀ A) ⟼₂ S
  }

open Signature L:Sig public
