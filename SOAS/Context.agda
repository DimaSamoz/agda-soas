{-# OPTIONS --rewriting #-}

-- Concrete definition of contexts over a sort T
module SOAS.Context {T : Set} where

open import SOAS.Common

open import Data.List using (List; []; _∷_; _++_)
open import Agda.Builtin.Equality.Rewrite


-- Context: a list of types
data Ctx : Set where
  ∅   : Ctx
  _∙_ : (α : T) → (Γ : Ctx) → Ctx
infixr 50 _∙_

-- Singleton context
pattern _⌋ τ = τ ∙ ∅
infixr 60 _⌋

-- _⌊_ : (Ctx → Set) → Ctx → Set
-- X ⌊ Γ = X Γ
-- infix 20 _⌊_
pattern ⌈_⌋ α = α ∙ ∅
infix 70 ⌈_⌋

pattern ⌊_ α = α
infix 70 ⌊_
--
-- pattern ⌊_⌋ τ = τ ∙ ∅
-- infix 70 ⌊_⌋

-- Context concatenation
_∔_ : Ctx → Ctx → Ctx
∅       ∔ Δ = Δ
(α ∙ Γ) ∔ Δ = α ∙ (Γ ∔ Δ)
infixl 20 _∔_

-- Context concatenation is associative
∔-assoc : (Γ Δ Θ : Ctx) → ((Γ ∔ Δ) ∔ Θ) ≡ (Γ ∔ (Δ ∔ Θ))
∔-assoc ∅ Δ Θ = refl
∔-assoc (α ∙ Γ) Δ Θ = cong (α ∙_) (∔-assoc Γ Δ Θ)

-- Empty context is right unit of context concatenation
∔-unitʳ : (Γ : Ctx) → Γ ∔ ∅ ≡ Γ
∔-unitʳ ∅ = refl
∔-unitʳ (α ∙ Γ) = cong (α ∙_) (∔-unitʳ Γ)

-- Fairly innocuous extension of Agda's rewrite rules to equate Γ ∔ ∅ with Γ
-- and associativity -- avoids lots of awkward rewrites or transports
{-# REWRITE ∔-unitʳ #-}
{-# REWRITE ∔-assoc #-}
