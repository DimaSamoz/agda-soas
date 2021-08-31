{-
This second-order signature was created from the following second-order syntax description:

syntax Monoid | M

type
  * : 0-ary

term
  unit : * | ε 
  add  : *  *  ->  * | _⊕_ l20

theory
  (εU⊕ᴸ) a |> add (unit, a) = a
  (εU⊕ᴿ) a |> add (a, unit) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
-}

module Monoid.Signature where

open import SOAS.Context

open import SOAS.Common


open import SOAS.Syntax.Signature *T public
open import SOAS.Syntax.Build *T public

-- Operator symbols
data Mₒ : Set where
  unitₒ addₒ : Mₒ

-- Term signature
M:Sig : Signature Mₒ
M:Sig = sig λ
  {  unitₒ  → ⟼₀ *
  ;  addₒ   → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  }

open Signature M:Sig public
