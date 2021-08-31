{-
This second-order signature was created from the following second-order syntax description:

syntax GroupAction | GA

type
  * : 0-ary
  X : 0-ary

term
  unit : * | ε 
  add  : *  *  ->  * | _⊕_ l20
  neg  : *  ->  * | ⊖_ r40
  act  : *  X  ->  X | _⊙_ r30

theory
  (εU⊕ᴸ) a |> add (unit, a) = a
  (εU⊕ᴿ) a |> add (a, unit) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
  (⊖N⊕ᴸ) a |> add (neg (a), a) = unit
  (⊖N⊕ᴿ) a |> add (a, neg (a)) = unit
  (εU⊙)      x : X |> act (unit,      x) = x
  (⊕A⊙) g h  x : X |> act (add(g, h), x) = act (g, act(h, x))
-}

module GroupAction.Signature where

open import SOAS.Context

-- Type declaration
data GAT : Set where
  * : GAT
  X : GAT



open import SOAS.Syntax.Signature GAT public
open import SOAS.Syntax.Build GAT public

-- Operator symbols
data GAₒ : Set where
  unitₒ addₒ negₒ actₒ : GAₒ

-- Term signature
GA:Sig : Signature GAₒ
GA:Sig = sig λ
  {  unitₒ  → ⟼₀ *
  ;  addₒ   → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  negₒ   → (⊢₀ *) ⟼₁ *
  ;  actₒ   → (⊢₀ *) , (⊢₀ X) ⟼₂ X
  }

open Signature GA:Sig public
