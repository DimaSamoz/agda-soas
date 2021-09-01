
open import SOAS.Metatheory.Syntax

-- Metatheory of a second-order syntax
module SOAS.Metatheory {T : Set} (Syn : Syntax {T}) where

open import SOAS.Families.Core {T}

open import SOAS.Abstract.ExpStrength

open Syntax Syn

open CompatStrengths ⅀:CS public renaming (CoalgStr to ⅀:Str ; ExpStr to ⅀:ExpStr)

open import SOAS.Metatheory.Algebra ⅀F public
open import SOAS.Metatheory.Monoid ⅀F ⅀:Str public

module Theory (𝔛 : Familyₛ) where
  open import SOAS.Metatheory.MetaAlgebra   ⅀F 𝔛 public
  open import SOAS.Metatheory.Semantics     ⅀F ⅀:Str 𝔛 (𝕋:Init 𝔛) public
  open import SOAS.Metatheory.Traversal     ⅀F ⅀:Str 𝔛 (𝕋:Init 𝔛) public
  open import SOAS.Metatheory.Renaming      ⅀F ⅀:Str 𝔛 (𝕋:Init 𝔛) public
  open import SOAS.Metatheory.Coalgebraic   ⅀F ⅀:Str 𝔛 (𝕋:Init 𝔛) public
  open import SOAS.Metatheory.Substitution  ⅀F ⅀:Str 𝔛 (𝕋:Init 𝔛) public
