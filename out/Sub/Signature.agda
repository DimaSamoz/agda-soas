{-
This second-order signature was created from the following second-order syntax description:

syntax Sub | S

type
  L : 0-ary
  T : 0-ary

term
  vr : L  ->  T
  sb : L.T  T  ->  T

theory
  (C) x y : T |> sb (a. x[], y[]) = x[]
  (L) x : T |> sb (a. vr(a), x[]) = x[]
  (R) a : L  x : L.T |> sb (b. x[b], vr(a[])) = x[a[]]
  (A) x : (L,L).T  y : L.T  z : T |> sb (a. sb (b. x[a,b], y[a]), z[]) = sb (b. sb (a. x[a, b], z[]), sb (a. y[a], z[]))
-}

module Sub.Signature where

open import SOAS.Context

-- Type declaration
data ST : Set where
  L : ST
  T : ST



open import SOAS.Syntax.Signature ST public
open import SOAS.Syntax.Build ST public

-- Operator symbols
data Sₒ : Set where
  vrₒ sbₒ : Sₒ

-- Term signature
S:Sig : Signature Sₒ
S:Sig = sig λ
  {  vrₒ  → (⊢₀ L) ⟼₁ T
  ;  sbₒ  → (L ⊢₁ T) , (⊢₀ T) ⟼₂ T
  }

open Signature S:Sig public
