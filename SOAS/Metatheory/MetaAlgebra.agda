
open import SOAS.Common
open import SOAS.Families.Core

-- Families with syntactic structure
module SOAS.Metatheory.MetaAlgebra {T : Set}
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ)
  (𝔛 : Familyₛ) where

open import SOAS.Context {T}
open import SOAS.Variable {T}
open import SOAS.Construction.Structure as Structure
open import SOAS.Abstract.Hom {T}
import SOAS.Abstract.Coalgebra {T} as →□ ; open →□.Sorted

open import SOAS.Metatheory.Algebra ⅀F

private
  variable
    Γ Δ Π : Ctx
    α : T

-- A family with support for variables, metavariables, and ⅀-algebra structure
record MetaAlg (𝒜 : Familyₛ) : Set where

  field
    𝑎𝑙𝑔  : ⅀ 𝒜 ⇾̣ 𝒜
    𝑣𝑎𝑟  :   ℐ ⇾̣ 𝒜
    𝑚𝑣𝑎𝑟 :   𝔛 ⇾̣ 〖 𝒜 , 𝒜 〗

  -- Congruence in metavariable arguments
  𝑚≈₁ : {𝔪₁ 𝔪₂ : 𝔛 α Π}{σ : Π ~[ 𝒜 ]↝ Γ}
      → 𝔪₁ ≡ 𝔪₂
      → 𝑚𝑣𝑎𝑟 𝔪₁ σ ≡ 𝑚𝑣𝑎𝑟 𝔪₂ σ
  𝑚≈₁ refl = refl

  𝑚≈₂ : {𝔪 : 𝔛 α Π}{σ ς : Π ~[ 𝒜 ]↝ Γ}
      → ({τ : T}(v : ℐ τ Π) → σ v ≡ ς v)
      → 𝑚𝑣𝑎𝑟 𝔪 σ ≡ 𝑚𝑣𝑎𝑟 𝔪 ς
  𝑚≈₂ {𝔪 = 𝔪} p = cong (𝑚𝑣𝑎𝑟 𝔪) (dext p)

-- Meta-algebra homomorphism
record MetaAlg⇒ {𝒜 ℬ : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜)(ℬᵃ : MetaAlg ℬ)
                (f : 𝒜 ⇾̣ ℬ) : Set where
  private module 𝒜 = MetaAlg 𝒜ᵃ
  private module ℬ = MetaAlg ℬᵃ

  field
    ⟨𝑎𝑙𝑔⟩  : {t : ⅀ 𝒜 α Γ} → f (𝒜.𝑎𝑙𝑔 t) ≡ ℬ.𝑎𝑙𝑔 (⅀₁ f t)
    ⟨𝑣𝑎𝑟⟩  : {v : ℐ α Γ} → f (𝒜.𝑣𝑎𝑟 v) ≡ ℬ.𝑣𝑎𝑟 v
    ⟨𝑚𝑣𝑎𝑟⟩ : {𝔪 : 𝔛 α Π}{ε : Π ~[ 𝒜 ]↝ Γ} → f (𝒜.𝑚𝑣𝑎𝑟 𝔪 ε) ≡ ℬ.𝑚𝑣𝑎𝑟 𝔪 (f ∘ ε)

-- Category of meta-algebras
module MetaAlgebraStructure = Structure 𝔽amiliesₛ MetaAlg

MetaAlgebraCatProps : MetaAlgebraStructure.CategoryProps
MetaAlgebraCatProps = record
  { IsHomomorphism = MetaAlg⇒
  ; id-hom = λ {𝒜}{𝒜ᵃ} → record
    { ⟨𝑎𝑙𝑔⟩ = cong (𝑎𝑙𝑔 𝒜ᵃ) (sym ⅀.identity)
    ; ⟨𝑣𝑎𝑟⟩ = refl
    ; ⟨𝑚𝑣𝑎𝑟⟩ = refl }
  ; comp-hom = λ{ {𝐶ˢ = 𝒜ᵃ}{ℬᵃ}{𝒞ᵃ} g f gᵃ⇒ fᵃ⇒ → record
    { ⟨𝑎𝑙𝑔⟩ = trans (cong g (⟨𝑎𝑙𝑔⟩ fᵃ⇒))
            (trans (⟨𝑎𝑙𝑔⟩  gᵃ⇒)
                    (cong (𝑎𝑙𝑔 𝒞ᵃ) (sym ⅀.homomorphism)))
    ; ⟨𝑣𝑎𝑟⟩ = trans (cong g (⟨𝑣𝑎𝑟⟩ fᵃ⇒)) (⟨𝑣𝑎𝑟⟩ gᵃ⇒)
    ; ⟨𝑚𝑣𝑎𝑟⟩ = trans (cong g (⟨𝑚𝑣𝑎𝑟⟩ fᵃ⇒)) (⟨𝑚𝑣𝑎𝑟⟩ gᵃ⇒) }
  }} where open MetaAlg ; open MetaAlg⇒

module MetaAlgProps = MetaAlgebraStructure.CategoryProps MetaAlgebraCatProps

𝕄etaAlgebras : Category 1ℓ 0ℓ 0ℓ
𝕄etaAlgebras = MetaAlgebraStructure.StructCat MetaAlgebraCatProps

module 𝕄etaAlg = Category 𝕄etaAlgebras


MetaAlgebra : Set₁
MetaAlgebra = 𝕄etaAlg.Obj

MetaAlgebra⇒ : MetaAlgebra → MetaAlgebra → Set
MetaAlgebra⇒ = 𝕄etaAlg._⇒_


-- module AsMetaAlg (𝒜ᵃ : MetaAlgebra) where
--   open Object 𝒜ᵃ renaming (𝐶 to 𝒜 ; ˢ to ᵃ) public
--   open MetaAlg ᵃ public
--
-- module AsMetaAlg⇒ {𝒜ᵃ ℬᵃ : MetaAlgebra} (fᵃ⇒ : MetaAlgebra⇒ 𝒜ᵃ ℬᵃ) where
--   open Morphism fᵃ⇒ renaming (𝑓 to f ; ˢ⇒ to ᵃ⇒) public
--   open MetaAlg⇒ ᵃ⇒ public

-- Identity is a meta-algebra homomorphism
idᵃ : {𝒜 : Familyₛ} → (𝒜ᵃ : MetaAlg 𝒜) → MetaAlg⇒ 𝒜ᵃ 𝒜ᵃ id
idᵃ 𝒜ᵃ = record { ⟨𝑎𝑙𝑔⟩ = cong (MetaAlg.𝑎𝑙𝑔 𝒜ᵃ) (sym ⅀.identity)
                ; ⟨𝑣𝑎𝑟⟩ = refl ; ⟨𝑚𝑣𝑎𝑟⟩ = refl }
