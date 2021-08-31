{-
This second-order signature was created from the following second-order syntax description:

syntax Combinatory | CL

type
  * : 0-ary

term
  app : *  *  ->  * | _$_ l20
  i   : *
  k   : *
  s   : *

theory
  (IA) x     |> app (i, x) = x
  (KA) x y   |> app (app(k, x), y) = x
  (SA) x y z |> app (app (app (s, x), y), z) = app (app(x, z), app(y, z))
-}

module Combinatory.Signature where

open import SOAS.Context

open import SOAS.Common


open import SOAS.Syntax.Signature *T public
open import SOAS.Syntax.Build *T public

-- Operator symbols
data CLₒ : Set where
  appₒ iₒ kₒ sₒ : CLₒ

-- Term signature
CL:Sig : Signature CLₒ
CL:Sig = sig λ
  {  appₒ  → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  iₒ    → ⟼₀ *
  ;  kₒ    → ⟼₀ *
  ;  sₒ    → ⟼₀ *
  }

open Signature CL:Sig public
