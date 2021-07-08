
-- Concrete definition of variables, context maps, and map operations
module SOAS.Variable {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Sorting
open import SOAS.Families.Core {T}


-- Sorted family of variables, as typed, scoped de Bruijn indices
data ℐ : Familyₛ where
  new : {α   : T}{Γ : Ctx}          → ℐ α (α ∙ Γ)
  old : {α β : T}{Γ : Ctx} → ℐ β Γ → ℐ β (α ∙ Γ)

-- Explicitly specify the extra variable type
oldₑ : (α {β} : T)(Γ : Ctx) → ℐ β Γ → ℐ β (α ∙ Γ)
oldₑ α Γ = old {α}{_}{Γ}


-- | Context-family maps
-- Generalised transformations between 𝒳-terms in one context and 𝒴-terms in
-- another context. The special case of 𝒳 being the family of variables
-- gives the usual notion of an environment (Allais et al.) or "type preserving
-- map from variables over Γ to stuff over Δ" (McBride 2005), where "stuff" is a
-- sorted family.

-- Context-family map between two sorted families in different contexts.
-- The type is implicitly quantified over.
_~[_➔_]↝_ : Ctx → Familyₛ → Familyₛ → Ctx → Set
Γ ~[ 𝒳 ➔ 𝒴 ]↝ Δ = {τ : T} → 𝒳 τ Γ → 𝒴 τ Δ

-- 𝒳-valued context map, associating variables in context Γ with 𝒳-terms
-- in context Δ.
_~[_]↝_ : Ctx → Familyₛ → Ctx → Set
Γ ~[ 𝒳 ]↝ Δ = Γ ~[ ℐ ➔ 𝒳 ]↝ Δ
infix 10 _~[_]↝_

-- Renaming map, mapping variables to variables
_↝_ : Ctx → Ctx → Set
Γ ↝ Δ = Γ ~[ ℐ ]↝ Δ
infix 4 _↝_
