

open import SOAS.Common
open import SOAS.Families.Core
import SOAS.Metatheory.SynAlgebra

-- Shorthands for de Bruijn indices
module SOAS.Syntax.Shorthands {T : Set}
  {⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ}
  (open SOAS.Metatheory.SynAlgebra ⅀F)
  {𝒜 : Familyₛ → Familyₛ}(𝒜ᵃ : (𝔛 : Familyₛ) → SynAlg 𝔛 (𝒜 𝔛))
  where

open import SOAS.Context
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive
open import SOAS.Variable
open import Data.Nat

open import Relation.Nullary.Decidable using (True; toWitness)

private
  variable
    α β γ δ υ : T
    Γ Δ : Ctx

module _ {𝔛 : Familyₛ} where
  open SynAlg 𝔛 (𝒜ᵃ 𝔛)

  -- Refer to variables via de Bruijn numerals: e.g. ` 2 = 𝑣𝑎𝑟 (old (old new))
  len : Ctx {T} → ℕ
  len ∅        =  ℕ.zero
  len (α ∙ Γ)  =  suc (len Γ)

  ix : {Γ : Ctx} → {n : ℕ} → (p : n < len Γ) → T
  ix {(α ∙ _)} {zero}    (s≤s z≤n)  =  α
  ix {(_ ∙ Γ)} {(suc n)} (s≤s p)    =  ix p

  deBruijn : ∀ {Γ} → {n : ℕ} → (p : n < len Γ) → ℐ (ix p) Γ
  deBruijn {_ ∙ _} {zero}    (s≤s z≤n)  =  new
  deBruijn {_ ∙ Γ} {(suc n)} (s≤s p)    =  old (deBruijn p)

  ′ : {Γ : Ctx}(n : ℕ){n∈Γ : True (suc n ≤? len Γ)} → 𝒜 𝔛 (ix (toWitness n∈Γ)) Γ
  ′ n {n∈Γ} = 𝑣𝑎𝑟 (deBruijn (toWitness n∈Γ))

  -- Explicit abbreviations for de Bruijn indices 0-4
  x₀ : 𝒜 𝔛 α (α ∙ Γ)
  x₀ = 𝑣𝑎𝑟 new
  x₁ : 𝒜 𝔛 β (α ∙ β ∙ Γ)
  x₁ = 𝑣𝑎𝑟 (old new)
  x₂ : 𝒜 𝔛 γ (α ∙ β ∙ γ ∙ Γ)
  x₂ = 𝑣𝑎𝑟 (old (old new))
  x₃ : 𝒜 𝔛 δ (α ∙ β ∙ γ ∙ δ ∙ Γ)
  x₃ = 𝑣𝑎𝑟 (old (old (old new)))
  x₄ : 𝒜 𝔛 υ (α ∙ β ∙ γ ∙ δ ∙ υ ∙ Γ)
  x₄ = 𝑣𝑎𝑟 (old (old (old (old new))))
