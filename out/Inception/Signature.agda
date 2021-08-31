{-
This second-order signature was created from the following second-order syntax description:

syntax Inception | IA

type
  L : 0-ary
  P : 0-ary
  A : 0-ary

term
  rec : L  P  ->  A
  inc : L.A  P.A  ->  A

theory
  (S) p : P   a : P.A |> inc (l. rec (l, p[]), x. a[x]) = a[p[]]
  (E) a : L.A  |> k : L |- inc (l. a[l], x. rec(k, x)) = a[k]
  (W) m : A  a : P.A  |> inc (l. m[], x. a[x]) = m[]
  (A) p : (L,L).A  a : (L,P).A  b : P.A |>         inc (l. inc (k. p[l, k], x. a[l,x]), y. b[y])       = inc (k. inc(l. p[l,k], y.b[y]), x. inc(l. a[l,x], y.b[y]))
-}

module Inception.Signature where

open import SOAS.Context

-- Type declaration
data IAT : Set where
  L : IAT
  P : IAT
  A : IAT



open import SOAS.Syntax.Signature IAT public
open import SOAS.Syntax.Build IAT public

-- Operator symbols
data IAₒ : Set where
  recₒ incₒ : IAₒ

-- Term signature
IA:Sig : Signature IAₒ
IA:Sig = sig λ
  {  recₒ  → (⊢₀ L) , (⊢₀ P) ⟼₂ A
  ;  incₒ  → (L ⊢₁ A) , (P ⊢₁ A) ⟼₂ A
  }

open Signature IA:Sig public
