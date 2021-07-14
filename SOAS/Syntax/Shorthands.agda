

open import SOAS.Common
open import SOAS.Families.Core
import SOAS.Metatheory.MetaAlgebra

-- Shorthands for de Bruijn indices
module SOAS.Syntax.Shorthands {T : Set}
  {⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ}
  (open SOAS.Metatheory.MetaAlgebra ⅀F)
  {𝒜 : {Familyₛ} → Familyₛ}(𝒜ᵃ : (𝔛 : Familyₛ) → MetaAlg 𝔛 (𝒜 {𝔛}))
  where

open import SOAS.Context
open import SOAS.Variable
open import Data.Nat
open import Data.Empty

private
  variable
    α β γ δ υ : T
    Γ Δ : Ctx

module _ {𝔛 : Familyₛ} where
  open MetaAlg 𝔛 (𝒜ᵃ 𝔛)

  index : Ctx → ℕ → T
  index ∅ n = ⊥-elim impossible where postulate impossible : ⊥
  index (α ∙ Γ) 0 = α
  index (α ∙ Γ) (suc n) = index Γ n

  deBruijn : (n : ℕ) → ℐ (index Γ n) Γ
  deBruijn {α ∙ Γ} 0 = new
  deBruijn {α ∙ Γ} (suc n) = old (deBruijn n)
  deBruijn {∅}     _       = ⊥-elim impossible where postulate impossible : ⊥

  ′ : {Γ : Ctx}(n : ℕ) → 𝒜 (index Γ n) Γ
  ′ n = 𝑣𝑎𝑟 (deBruijn n)

  x₀ : 𝒜 α (α ∙ Γ)
  x₀ = 𝑣𝑎𝑟 new
  x₁ : 𝒜 β (α ∙ β ∙ Γ)
  x₁ = 𝑣𝑎𝑟 (old new)
  x₂ : 𝒜 γ (α ∙ β ∙ γ ∙ Γ)
  x₂ = 𝑣𝑎𝑟 (old (old new))
  x₃ : 𝒜 δ (α ∙ β ∙ γ ∙ δ ∙ Γ)
  x₃ = 𝑣𝑎𝑟 (old (old (old new)))
  x₄ : 𝒜 υ (α ∙ β ∙ γ ∙ δ ∙ υ ∙ Γ)
  x₄ = 𝑣𝑎𝑟 (old (old (old (old new))))
