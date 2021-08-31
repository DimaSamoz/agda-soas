{-
This second-order signature was created from the following second-order syntax description:

syntax Ring | R

type
  * : 0-ary

term
  zero : * | 𝟘 
  add  : *  *  ->  * | _⊕_ l20
  one  : * | 𝟙 
  mult : *  *  ->  * | _⊗_ l30
  neg  : *  ->  * | ⊖_ r50

theory
  (𝟘U⊕ᴸ) a |> add (zero, a) = a
  (𝟘U⊕ᴿ) a |> add (a, zero) = a
  (⊕A) a b c |> add (add(a, b), c) = add (a, add(b, c))
  (⊕C) a b |> add(a, b) = add(b, a)
  (𝟙U⊗ᴸ) a |> mult (one, a) = a
  (𝟙U⊗ᴿ) a |> mult (a, one) = a
  (⊗A) a b c |> mult (mult(a, b), c) = mult (a, mult(b, c))
  (⊗D⊕ᴸ) a b c |> mult (a, add (b, c)) = add (mult(a, b), mult(a, c))
  (⊗D⊕ᴿ) a b c |> mult (add (a, b), c) = add (mult(a, c), mult(b, c))
  (𝟘X⊗ᴸ) a |> mult (zero, a) = zero
  (𝟘X⊗ᴿ) a |> mult (a, zero) = zero
  (⊖N⊕ᴸ) a |> add (neg (a), a) = zero
  (⊖N⊕ᴿ) a |> add (a, neg (a)) = zero
-}

module Ring.Signature where

open import SOAS.Context

open import SOAS.Common


open import SOAS.Syntax.Signature *T public
open import SOAS.Syntax.Build *T public

-- Operator symbols
data Rₒ : Set where
  zeroₒ addₒ oneₒ multₒ negₒ : Rₒ

-- Term signature
R:Sig : Signature Rₒ
R:Sig = sig λ
  {  zeroₒ  → ⟼₀ *
  ;  addₒ   → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  oneₒ   → ⟼₀ *
  ;  multₒ  → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  negₒ   → (⊢₀ *) ⟼₁ *
  }

open Signature R:Sig public
