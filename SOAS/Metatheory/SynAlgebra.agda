
open import SOAS.Common
import SOAS.Families.Core

-- Families with syntactic structure
module SOAS.Metatheory.SynAlgebra {T : Set}
  (open SOAS.Families.Core {T})
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
record SynAlg (𝒜 : Familyₛ) : Set where

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

-- Syntactic algebra homomorphism
record SynAlg⇒ {𝒜 ℬ : Familyₛ}(𝒜ᵃ : SynAlg 𝒜)(ℬᵃ : SynAlg ℬ)
                (f : 𝒜 ⇾̣ ℬ) : Set where
  private module 𝒜 = SynAlg 𝒜ᵃ
  private module ℬ = SynAlg ℬᵃ

  field
    ⟨𝑎𝑙𝑔⟩  : {t : ⅀ 𝒜 α Γ} → f (𝒜.𝑎𝑙𝑔 t) ≡ ℬ.𝑎𝑙𝑔 (⅀₁ f t)
    ⟨𝑣𝑎𝑟⟩  : {v : ℐ α Γ} → f (𝒜.𝑣𝑎𝑟 v) ≡ ℬ.𝑣𝑎𝑟 v
    ⟨𝑚𝑣𝑎𝑟⟩ : {𝔪 : 𝔛 α Π}{ε : Π ~[ 𝒜 ]↝ Γ} → f (𝒜.𝑚𝑣𝑎𝑟 𝔪 ε) ≡ ℬ.𝑚𝑣𝑎𝑟 𝔪 (f ∘ ε)

-- Category of syntactic algebras
module SynAlgebraStructure = Structure 𝔽amiliesₛ SynAlg

SynAlgebraCatProps : SynAlgebraStructure.CategoryProps
SynAlgebraCatProps = record
  { IsHomomorphism = SynAlg⇒
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
  }} where open SynAlg ; open SynAlg⇒

module SynAlgProps = SynAlgebraStructure.CategoryProps SynAlgebraCatProps

𝕊ynAlgebras : Category 1ℓ 0ℓ 0ℓ
𝕊ynAlgebras = SynAlgebraStructure.StructCat SynAlgebraCatProps

module 𝕊ynAlg = Category 𝕊ynAlgebras

SynAlgebra : Set₁
SynAlgebra = 𝕊ynAlg.Obj

SynAlgebra⇒ : SynAlgebra → SynAlgebra → Set
SynAlgebra⇒ = 𝕊ynAlg._⇒_



-- Identity is a syntactic algebra homomorphism
idᵃ : {𝒜 : Familyₛ} → (𝒜ᵃ : SynAlg 𝒜) → SynAlg⇒ 𝒜ᵃ 𝒜ᵃ id
idᵃ 𝒜ᵃ = record { ⟨𝑎𝑙𝑔⟩ = cong (SynAlg.𝑎𝑙𝑔 𝒜ᵃ) (sym ⅀.identity)
                ; ⟨𝑣𝑎𝑟⟩ = refl ; ⟨𝑚𝑣𝑎𝑟⟩ = refl }
