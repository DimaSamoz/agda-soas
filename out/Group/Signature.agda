{-
This second-order signature was created from the following second-order syntax description:

syntax Group | G

type
  * : 0-ary

term
  unit : * | ε 
  add  : *  *  ->  * | _⊕_ l20
  neg  : *  ->  * | ⊖_ r40

theory
  (εU⊕ᴸ) a |> add (unit, a) = a
  (εU⊕ᴿ) a |> add (a, unit) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
  (⊖N⊕ᴸ) a |> add (neg (a), a) = unit
  (⊖N⊕ᴿ) a |> add (a, neg (a)) = unit
-}

module Group.Signature where

open import SOAS.Context

open import SOAS.Common


open import SOAS.Syntax.Signature *T public
open import SOAS.Syntax.Build *T public

-- Operator symbols
data Gₒ : Set where
  unitₒ addₒ negₒ : Gₒ

-- Term signature
G:Sig : Signature Gₒ
G:Sig = sig λ
  {  unitₒ  → ⟼₀ *
  ;  addₒ   → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  negₒ   → (⊢₀ *) ⟼₁ *
  }

open Signature G:Sig public
