{-
This second-order signature was created from the following second-order syntax description:

syntax STLC | Λ

type
  N   : 0-ary
  _↣_ : 2-ary | r30

term
  app : α ↣ β  α  ->  β | _$_ l20
  lam : α.β  ->  α ↣ β | ƛ_ r10

theory
  (ƛβ) b : α.β  a : α |> app (lam(x.b[x]), a) = b[a]
  (ƛη) f : α ↣ β      |> lam (x. app(f, x))   = f
-}

module STLC.Signature where

open import SOAS.Context

-- Type declaration
data ΛT : Set where
  N   : ΛT
  _↣_ : ΛT → ΛT → ΛT
infixr 30 _↣_


open import SOAS.Syntax.Signature ΛT public
open import SOAS.Syntax.Build ΛT public

-- Operator symbols
data Λₒ : Set where
  appₒ lamₒ : {α β : ΛT} → Λₒ

-- Term signature
Λ:Sig : Signature Λₒ
Λ:Sig = sig λ
  { (appₒ {α}{β}) → (⊢₀ α ↣ β) , (⊢₀ α) ⟼₂ β
  ; (lamₒ {α}{β}) → (α ⊢₁ β) ⟼₁ α ↣ β
  }

open Signature Λ:Sig public
