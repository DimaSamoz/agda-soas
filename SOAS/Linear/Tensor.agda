
-- Linear tensor product of families
module SOAS.Linear.Tensor {T : Set} where

open import SOAS.Families.Core {T}
open import SOAS.Context
open import SOAS.Variable

open import SOAS.Common

-- Day convolution of families
data _⊗_ (X Y : Family) : Ctx → Set where
  _⊹_ : {Γ Δ : Ctx} → X Γ → Y Δ → (X ⊗ Y) (Γ ∔ Δ)
infixr 30 _⊗_

infix 30 _⊹_
