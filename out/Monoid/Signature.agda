{-
This file was created from the following second-order syntax description:

type *T
  * : 0-ary

term A
  unit : * | ε
  mult : *  *  ->  * | _+_ l20
-}

module Monoid.Signature where

open import SOAS.Context

-- Type declaration
data *T : Set where
  * : *T



open import SOAS.Syntax.Signature *T public
open import SOAS.Syntax.Build *T public

-- Operator symbols
data Aₒ : Set where
  unitₒ multₒ : Aₒ

-- Term signature
A:Sig : Signature Aₒ
A:Sig = sig λ
  {  unitₒ  → ⟼₀ *
  ;  multₒ  → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  }

open Signature A:Sig public
