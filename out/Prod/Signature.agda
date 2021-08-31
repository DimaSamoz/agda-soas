{-
This second-order signature was created from the following second-order syntax description:

syntax Prod | P

type
  _⊗_ : 2-ary | l40

term
  pair : α  β  ->  α ⊗ β | ⟨_,_⟩ 
  fst  : α ⊗ β  ->  α
  snd  : α ⊗ β  ->  β

theory
  (fβ) a : α  b : β |> fst (pair(a, b))      = a
  (sβ) a : α  b : β |> snd (pair(a, b))      = b
  (pη) p : α ⊗ β    |> pair (fst(p), snd(p)) = p
-}

module Prod.Signature where

open import SOAS.Context

-- Type declaration
data PT : Set where
  _⊗_ : PT → PT → PT
infixl 40 _⊗_


open import SOAS.Syntax.Signature PT public
open import SOAS.Syntax.Build PT public

-- Operator symbols
data Pₒ : Set where
  pairₒ fstₒ sndₒ : {α β : PT} → Pₒ

-- Term signature
P:Sig : Signature Pₒ
P:Sig = sig λ
  { (pairₒ {α}{β}) → (⊢₀ α) , (⊢₀ β) ⟼₂ α ⊗ β
  ; (fstₒ  {α}{β}) → (⊢₀ α ⊗ β) ⟼₁ α
  ; (sndₒ  {α}{β}) → (⊢₀ α ⊗ β) ⟼₁ β
  }

open Signature P:Sig public
