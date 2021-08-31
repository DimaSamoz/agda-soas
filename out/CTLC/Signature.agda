{-
This second-order signature was created from the following second-order syntax description:

syntax CTLC | ΛC

type
  N   : 0-ary
  _↣_ : 2-ary | r30
  ¬_  : 1-ary | r30

term
  app    : α ↣ β  α  ->  β | _$_ l20
  lam    : α.β  ->  α ↣ β | ƛ_ r10
  throw  : α  ¬ α  ->  β
  callcc : ¬ α.α  ->  α

theory
  (ƛβ) b : α.β  a : α |> app (lam(x.b[x]), a) = b[a]
  (ƛη) f : α ↣ β      |> lam (x. app(f, x))   = f
-}

module CTLC.Signature where

open import SOAS.Context

-- Type declaration
data ΛCT : Set where
  N   : ΛCT
  _↣_ : ΛCT → ΛCT → ΛCT
  ¬_  : ΛCT → ΛCT
infixr 30 _↣_
infixr 30 ¬_


open import SOAS.Syntax.Signature ΛCT public
open import SOAS.Syntax.Build ΛCT public

-- Operator symbols
data ΛCₒ : Set where
  appₒ lamₒ throwₒ : {α β : ΛCT} → ΛCₒ
  callccₒ : {α : ΛCT} → ΛCₒ

-- Term signature
ΛC:Sig : Signature ΛCₒ
ΛC:Sig = sig λ
  { (appₒ    {α}{β}) → (⊢₀ α ↣ β) , (⊢₀ α) ⟼₂ β
  ; (lamₒ    {α}{β}) → (α ⊢₁ β) ⟼₁ α ↣ β
  ; (throwₒ  {α}{β}) → (⊢₀ α) , (⊢₀ ¬ α) ⟼₂ β
  ; (callccₒ {α})    → (¬ α ⊢₁ α) ⟼₁ α
  }

open Signature ΛC:Sig public
