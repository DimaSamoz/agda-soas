{-
This second-order signature was created from the following second-order syntax description:

syntax Monad | M

type
  T : 1-ary

term
  ret  : α  ->  T α
  bind : T α  α.(T β)  ->  T β | _>>=_ r10

theory
  (LU) a : α   b : α.(T β) |> bind (ret(a), x. b[x]) =  b[a]
  (RU) t : T α |> bind (t, x. ret(x)) = t
  (AS) t : T α  b : α.(T β)  c : β.(T γ) |> bind (bind (t, x.b[x]), y.c[y]) = bind (t, x. bind (b[x], y.c[y]))
-}

module Monad.Signature where

open import SOAS.Context

-- Type declaration
data MT : Set where
  T : MT → MT



open import SOAS.Syntax.Signature MT public
open import SOAS.Syntax.Build MT public

-- Operator symbols
data Mₒ : Set where
  retₒ : {α : MT} → Mₒ
  bindₒ : {α β : MT} → Mₒ

-- Term signature
M:Sig : Signature Mₒ
M:Sig = sig λ
  { (retₒ  {α})    → (⊢₀ α) ⟼₁ T α
  ; (bindₒ {α}{β}) → (⊢₀ T α) , (α ⊢₁ T β) ⟼₂ T β
  }

open Signature M:Sig public
