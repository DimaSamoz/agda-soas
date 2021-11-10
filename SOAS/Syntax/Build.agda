
-- Helper operations to construct and build signatures
module SOAS.Syntax.Build (T : Set) where

open import SOAS.Common
open import SOAS.Families.Build {T}
open import SOAS.Context {T}
open import Data.List.Base

open import SOAS.Syntax.Signature T

-- Syntactic sugar to construct arity - sort mappings
⟼₀_ : T → List (Ctx × T) × T
⟼₀_ τ = [] , τ

_⟼₁_ : (Ctx × T) → T → List (Ctx × T) × T
a ⟼₁ τ = [ a ] , τ

_,_⟼₂_ : (a₁ a₂ : Ctx × T) → T → List (Ctx × T) × T
a₁ , a₂ ⟼₂ τ = (a₁ ∷ [ a₂ ]) , τ

_,_,_⟼₃_ : (a₁ a₂ a₃ : Ctx × T) → T → List (Ctx × T) × T
a₁ , a₂ , a₃ ⟼₃ τ = (a₁ ∷ a₂ ∷ [ a₃ ]) , τ

_⟼ₙ_ : List (Ctx × T) → T → List (Ctx × T) × T
_⟼ₙ_ = _,_

-- Syntactic sugar to costruct arguments
⊢₀_ : T → Ctx × T
⊢₀ α = ∅ , α

_⊢₁_ : T → T → Ctx × T
τ ⊢₁ α = ⌊ τ ⌋ , α

_,_⊢₂_ : (τ₁ τ₂ : T) → T → Ctx × T
τ₁ , τ₂ ⊢₂ α = ⌊ τ₁ ∙ τ₂ ⌋ , α

_,_,_⊢₃_ : (τ₁ τ₂ τ₃ : T) → T → Ctx × T
τ₁ , τ₂ , τ₃ ⊢₃ α = ⌊ τ₁ ∙ τ₂ ∙ τ₃ ⌋ , α

_⊢ₙ_ : Ctx → T → Ctx × T
Π ⊢ₙ τ = Π , τ

infix 2 ⟼₀_
infix 2 _⟼₁_
infix 2 _,_⟼₂_
infix 2 _,_,_⟼₃_
infix 2 _⟼ₙ_

infix 10 ⊢₀_
infix 10 _⊢₁_
infix 10 _,_⊢₂_
infix 10 _⊢ₙ_


-- Sum of two signatures
_+ˢ_ : {O₁ O₂ : Set} → Signature O₁ → Signature O₂ → Signature (+₂ O₁ O₂)
S1 +ˢ S2 = sig (₂| ∣ S1 ∣ ∣ S2 ∣)
  where open Signature

-- Sums of signatures
Σ₂ : {O₁ O₂ : Set} → Signature O₁ → Signature O₂ → Signature (+₂ O₁ O₂)
Σ₂ S₁ S₂ = sig (₂| (∣ S₁ ∣) (∣ S₂ ∣))
  where open Signature

Σ₃ : {O₁ O₂ O₃ : Set} → Signature O₁ → Signature O₂ → Signature O₃ → Signature (+₃ O₁ O₂ O₃)
Σ₃ S₁ S₂ S₃ = sig (₃| (∣ S₁ ∣) (∣ S₂ ∣) (∣ S₃ ∣))
  where open Signature

Σ₄ : {O₁ O₂ O₃ O₄ : Set} → Signature O₁ → Signature O₂ → Signature O₃ → Signature O₄ → Signature (+₄ O₁ O₂ O₃ O₄)
Σ₄ S₁ S₂ S₃ S₄ = sig (₄| (∣ S₁ ∣) (∣ S₂ ∣) (∣ S₃ ∣) (∣ S₄ ∣))
  where open Signature
