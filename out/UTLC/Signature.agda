{-
This second-order signature was created from the following second-order syntax description:

syntax UTLC | Λ

type
  * : 0-ary

term
  app  : *  *  ->  * | _$_ l20
  lam  : *.*  ->  * | ƛ_ r10

theory
  (ƛβ) b : *.*  a : * |> app (lam (x.b[x]), a) = b[a]
  (ƛη) f : *          |> lam (x.app (f, x))    = f
  (lβ) b : *.*  a : * |> letd (a, x. b) = b[a]
-}

module UTLC.Signature where

open import SOAS.Context

open import SOAS.Common


open import SOAS.Syntax.Signature *T public
open import SOAS.Syntax.Build *T public

-- Operator symbols
data Λₒ : Set where
  appₒ lamₒ : Λₒ

-- Term signature
Λ:Sig : Signature Λₒ
Λ:Sig = sig λ
  {  appₒ   → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  lamₒ   → (* ⊢₁ *) ⟼₁ *
  }

open Signature Λ:Sig public
