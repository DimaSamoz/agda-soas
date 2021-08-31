{-
This second-order signature was created from the following second-order syntax description:

syntax CommMonoid | CM

type
  * : 0-ary

term
  unit : * | ε 
  add  : *  *  ->  * | _⊕_ l20

theory
  (εU⊕ᴸ) a |> add (unit, a) = a
  (εU⊕ᴿ) a |> add (a, unit) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
  (⊕C) a b |> add(a, b) = add(b, a)
-}

module CommMonoid.Signature where

open import SOAS.Context

open import SOAS.Common


open import SOAS.Syntax.Signature *T public
open import SOAS.Syntax.Build *T public

-- Operator symbols
data CMₒ : Set where
  unitₒ addₒ : CMₒ

-- Term signature
CM:Sig : Signature CMₒ
CM:Sig = sig λ
  {  unitₒ  → ⟼₀ *
  ;  addₒ   → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  }

open Signature CM:Sig public
