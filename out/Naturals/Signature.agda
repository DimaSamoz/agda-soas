{-
This second-order signature was created from the following second-order syntax description:

syntax Naturals | Nat

type
  N : 0-ary

term
  ze   : N
  su   : N  ->  N
  nrec : N  α  (α,N).α  ->  α

theory
  (zeβ) z : α   s : (α,N).α        |> nrec (ze,       z, r m. s[r,m]) = z
  (suβ) z : α   s : (α,N).α  n : N |> nrec (su (n), z, r m. s[r,m]) = s[nrec (n, z, r m. s[r,m]), n]
-}

module Naturals.Signature where

open import SOAS.Context

-- Type declaration
data NatT : Set where
  N : NatT



open import SOAS.Syntax.Signature NatT public
open import SOAS.Syntax.Build NatT public

-- Operator symbols
data Natₒ : Set where
  zeₒ suₒ : Natₒ
  nrecₒ : {α : NatT} → Natₒ

-- Term signature
Nat:Sig : Signature Natₒ
Nat:Sig = sig λ
  {  zeₒ        → ⟼₀ N
  ;  suₒ        → (⊢₀ N) ⟼₁ N
  ; (nrecₒ {α}) → (⊢₀ N) , (⊢₀ α) , (α , N ⊢₂ α) ⟼₃ α
  }

open Signature Nat:Sig public
