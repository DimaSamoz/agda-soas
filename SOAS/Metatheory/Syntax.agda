
-- Syntax of a second-order language
module SOAS.Metatheory.Syntax {T : Set} where

open import SOAS.Families.Core

open import SOAS.Common
open import SOAS.Context
open import Categories.Object.Initial
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive
open import SOAS.Coalgebraic.Strength
open import SOAS.Abstract.ExpStrength
open import SOAS.Metatheory.MetaAlgebra

-- Data characterising a second-order syntax:
-- * a signature endofunctor ⅀
-- * coalgebraic and exponential strength
-- * initial (⅀,𝔛)-meta-algebra for each 𝔛
-- + an inductive metavariable constructor for convenience
record Syntax : Set₁ where
  field
    ⅀F    : Functor 𝔽amiliesₛ 𝔽amiliesₛ
    ⅀:CS  : CompatStrengths ⅀F
    𝕋:Init : (𝔛 : Familyₛ) → Initial (𝕄etaAlgebras ⅀F 𝔛)
    mvarᵢ  : {𝔛 : Familyₛ}{τ : T}{Π Γ : Ctx} (open Initial (𝕋:Init 𝔛))
          → 𝔛 τ Π → Sub (𝐶 ⊥) Π Γ → 𝐶 ⊥ τ Γ

  module _ {𝔛 : Familyₛ} where
    open Initial (𝕋:Init 𝔛)

    _⟨_ : {τ : T}{Π Γ : Ctx} → 𝔛 τ Π → Sub (𝐶 ⊥) Π Γ → 𝐶 ⊥ τ Γ
    _⟨_ = mvarᵢ
    infix 30 _⟨_

    _⟨⟩ : {α : T}{Γ : Ctx} → 𝔛 α ∅ → 𝐶 ⊥ α Γ
    𝔪 ⟨⟩ =  𝔪 ⟨ •
    infix 50 _⟨⟩

  -- open CompatStrengths ⅀:CS public renaming (CoalgStr to ⅀:Str ; ExpStr to ⅀:ExpStr)
  --
  -- open import SOAS.Metatheory.Algebra ⅀F public
  -- open import SOAS.Metatheory.Monoid ⅀F ⅀:Str public
  --
  -- module Theory (𝔛 : Familyₛ) where
  --   open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛 public
  --   open import SOAS.Metatheory.Semantics ⅀F ⅀:Str 𝔛 (𝕋:Init 𝔛) public
  --   open import SOAS.Metatheory.Traversal ⅀F ⅀:Str 𝔛 (𝕋:Init 𝔛)  public
  --   open import SOAS.Metatheory.Renaming ⅀F ⅀:Str 𝔛 (𝕋:Init 𝔛) public
  --   open import SOAS.Metatheory.Coalgebraic ⅀F ⅀:Str 𝔛 (𝕋:Init 𝔛) public
  --   open import SOAS.Metatheory.Substitution ⅀F ⅀:Str 𝔛 (𝕋:Init 𝔛) public
