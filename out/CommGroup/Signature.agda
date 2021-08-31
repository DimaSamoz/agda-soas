{-
This second-order signature was created from the following second-order syntax description:

syntax CommGroup | CG

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
  (⊕C) a b |> add(a, b) = add(b, a)
-}

module CommGroup.Signature where

open import SOAS.Context

open import SOAS.Common


open import SOAS.Syntax.Signature *T public
open import SOAS.Syntax.Build *T public

-- Operator symbols
data CGₒ : Set where
  unitₒ addₒ negₒ : CGₒ

-- Term signature
CG:Sig : Signature CGₒ
CG:Sig = sig λ
  {  unitₒ  → ⟼₀ *
  ;  addₒ   → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  negₒ   → (⊢₀ *) ⟼₁ *
  }

open Signature CG:Sig public
