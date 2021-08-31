{-
This second-order signature was created from the following second-order syntax description:

syntax Sum | S

type
  _⊕_ : 2-ary | l30

term
  inl  : α  ->  α ⊕ β
  inr  : β  ->  α ⊕ β
  case : α ⊕ β  α.γ  β.γ  ->  γ

theory
  (lβ) a : α   f : α.γ  g : β.γ |> case (inl(a), x.f[x], y.g[y])      = f[a]
  (rβ) b : β   f : α.γ  g : β.γ |> case (inr(b), x.f[x], y.g[y])      = g[b]
  (cη) s : α ⊕ β  c : (α ⊕ β).γ |> case (s, x.c[inl(x)], y.c[inr(y)]) = c[s]
-}

module Sum.Signature where

open import SOAS.Context

-- Type declaration
data ST : Set where
  _⊕_ : ST → ST → ST
infixl 30 _⊕_


open import SOAS.Syntax.Signature ST public
open import SOAS.Syntax.Build ST public

-- Operator symbols
data Sₒ : Set where
  inlₒ inrₒ : {α β : ST} → Sₒ
  caseₒ : {α β γ : ST} → Sₒ

-- Term signature
S:Sig : Signature Sₒ
S:Sig = sig λ
  { (inlₒ  {α}{β})    → (⊢₀ α) ⟼₁ α ⊕ β
  ; (inrₒ  {α}{β})    → (⊢₀ β) ⟼₁ α ⊕ β
  ; (caseₒ {α}{β}{γ}) → (⊢₀ α ⊕ β) , (α ⊢₁ γ) , (β ⊢₁ γ) ⟼₃ γ
  }

open Signature S:Sig public
