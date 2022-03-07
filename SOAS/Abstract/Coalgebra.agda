
-- Category of □-coalgebras
module SOAS.Abstract.Coalgebra {T : Set} where

open import SOAS.Common
open import SOAS.Construction.Structure as Structure
open import SOAS.Context
open import SOAS.ContextMaps.Combinators
open import SOAS.ContextMaps.CategoryOfRenamings {T}
open import SOAS.Sorting
open import SOAS.Families.Core {T}
open import SOAS.Variable
open import SOAS.Families.BCCC
open import Data.Unit using (tt)

open import SOAS.Abstract.Hom {T}
import SOAS.Abstract.Box {T} as □

private
  variable
    α : T
    Γ Δ Θ : Ctx

-- Unsorted □-coalgebras
module Unsorted where
  open □.Unsorted
  record Coalg (X : Family) : Set where
    field
      r      : X ⇾ □ X
      counit : {t : X Γ} → r t id ≡ t
      comult : {ρ : Γ ↝ Δ}{ϱ : Δ ↝ Θ}{t : X Γ}
             → r t (ϱ ∘ ρ) ≡ r (r t ρ) ϱ

    -- Weakening of terms
    wkr : (Θ : Ctx) → X Γ → X (Θ ∔ Γ)
    wkr Θ t = r t (inr Θ)

    wkl : (Γ : Ctx) → X Γ → X (Γ ∔ Θ)
    wkl Γ t = r t (inl Γ)

    wk : X Γ → X (α ∙ Γ)
    wk t = r t old

  -- Unsorted coalgebra homomorphism
  record Coalg⇒ {X Y}(Xᵇ : Coalg X)(Yᵇ : Coalg Y) (f : X ⇾ Y) : Set where
    private module X = Coalg Xᵇ
    private module Y = Coalg Yᵇ
    field
      ⟨r⟩ : {ρ : Γ ↝ Δ}{t : X Γ} → f (X.r t ρ) ≡ Y.r (f t) (ρ)


  private module CoalgebraStructure = Structure 𝔽amilies Coalg

  -- Eilenberg–Moore category of a comonad
  ℂoalgebras : Category 1ℓ 0ℓ 0ℓ
  ℂoalgebras = CoalgebraStructure.StructCat (record
    { IsHomomorphism = Coalg⇒
    ; id-hom = record { ⟨r⟩ = refl }
    ; comp-hom = λ{ g f record { ⟨r⟩ = g⟨r⟩ } record { ⟨r⟩ = f⟨r⟩ } → record
      { ⟨r⟩ = trans (cong g f⟨r⟩) g⟨r⟩ } }
    })

  module ℂoalg = Category ℂoalgebras

  Coalgebra : Set₁
  Coalgebra = ℂoalg.Obj

  Coalgebra⇒ : Coalgebra → Coalgebra → Set
  Coalgebra⇒ = ℂoalg._⇒_


  module AsCoalgebra (Xᵇ : Coalgebra) where
    open Object Xᵇ public renaming (𝐶 to X ; ˢ to ᵇ)
    open Coalg ᵇ public

  -- Terminal object is a coalgebra
  ⊤ᵇ : Coalg ⊤ₘ
  ⊤ᵇ = record { r = λ _ _ → tt ; counit = refl ; comult = refl }

  -- □ X is the free coalgebra on X
  □ᵇ : (X : Family) → Coalg (□ X)
  □ᵇ X = record { r = λ b ρ ϱ → b (ϱ ∘ ρ) ; counit = refl ; comult = refl }



-- | Sorted □-coalgebras
module Sorted where
  open □.Sorted
  record Coalg (𝒳 : Familyₛ) : Set where
    field
      r      : 𝒳 ⇾̣ □ 𝒳
      counit : {t : 𝒳 α Γ} → r t id ≡ t
      comult : {ρ : Γ ↝ Δ}{ϱ : Δ ↝ Θ}{t : 𝒳 α Γ}
             → r t (ϱ ∘ ρ) ≡ r (r t ρ) ϱ

    -- Congruence in both arguments
    r≈₁ : {ρ : Γ ↝ Δ}{t₁ t₂ : 𝒳 α Γ} → t₁ ≡ t₂ → r t₁ ρ ≡ r t₂ ρ
    r≈₁ {ρ = ρ} p = cong (λ - → r - ρ) p

    r≈₂ : {ρ₁ ρ₂ : Γ ↝ Δ}{t : 𝒳 α Γ}
        → ({τ : T}{x : ℐ τ Γ} → ρ₁ x ≡ ρ₂ x)
        → r t ρ₁ ≡ r t ρ₂
    r≈₂ {t = t} p = cong (r t) (dext′ p)

    -- Weakening and associativity
    wkr : (Θ : Ctx) → 𝒳 α Γ → 𝒳 α (Θ ∔ Γ)
    wkr Θ t = r t (inr Θ)

    wkl : (Γ : Ctx) → 𝒳 α Γ → 𝒳 α (Γ ∔ Θ)
    wkl Γ t = r t (inl Γ)

    wk : {τ : T} → 𝒳 α Γ → 𝒳 α (τ ∙ Γ)
    wk t = r t old

    reassocʳ : (Γ Δ Θ : Ctx) → 𝒳 α ((Γ ∔ Δ) ∔ Θ) → 𝒳 α (Γ ∔ (Δ ∔ Θ))
    reassocʳ Γ Δ Θ t = r t (↝assocʳ Γ Δ Θ)

    reassocˡ : (Γ Δ Θ : Ctx) → 𝒳 α (Γ ∔ (Δ ∔ Θ)) → 𝒳 α ((Γ ∔ Δ) ∔ Θ)
    reassocˡ Γ Δ Θ t = r t (↝assocˡ Γ Δ Θ)

  -- Coalgebra homomorphism
  record Coalg⇒ {𝒳 𝒴}(Xᵇ : Coalg 𝒳)(𝒴ᵇ : Coalg 𝒴) (f : 𝒳 ⇾̣ 𝒴) : Set where
    private module 𝒳 = Coalg Xᵇ
    private module 𝒴 = Coalg 𝒴ᵇ
    field
      ⟨r⟩ : {ρ : Γ ↝ Δ}{t : 𝒳 α Γ} → f (𝒳.r t ρ) ≡ 𝒴.r (f t) (ρ)

  module CoalgebraStructure = Structure 𝔽amiliesₛ Coalg

  -- Eilenberg–Moore category of a comonad
  ℂoalgebras : Category 1ℓ 0ℓ 0ℓ
  ℂoalgebras = CoalgebraStructure.StructCat (record
    { IsHomomorphism = Coalg⇒
    ; id-hom = record { ⟨r⟩ = refl }
    ; comp-hom = λ{ g f record { ⟨r⟩ = g⟨r⟩ } record { ⟨r⟩ = f⟨r⟩ } → record
      { ⟨r⟩ = trans (cong g f⟨r⟩) g⟨r⟩ } }
    })

  module ℂoalg = Category ℂoalgebras

  Coalgebra : Set₁
  Coalgebra = ℂoalg.Obj

  Coalgebra⇒ : Coalgebra → Coalgebra → Set
  Coalgebra⇒ = ℂoalg._⇒_


  module AsCoalgebra (𝒳ᵇ : Coalgebra) where
    open Object 𝒳ᵇ public renaming (𝐶 to 𝒳 ; ˢ to ᵈ)

  -- 〖 𝒳 , 𝒴 〗 is a coalgebra for any 𝒳 and 𝒴
  〖_,_〗ᵇ : (𝒳 𝒴 : Familyₛ) → Coalg (〖 𝒳 , 𝒴 〗)
  〖 𝒳 , 𝒴 〗ᵇ = record { r = λ h ρ ϱ → h (ϱ ∘ ρ) ; counit = refl ; comult = refl }

  -- □ 𝒳 is the free coalgebra on 𝒳
  □ᵇ : (𝒳 : Familyₛ) → Coalg (□ 𝒳)
  □ᵇ 𝒳 = 〖 ℐ , 𝒳 〗ᵇ

  -- Pointed coalgebra
  record Coalgₚ (𝒳 : Familyₛ) : Set where

    field
      ᵇ : Coalg 𝒳
      η : ℐ ⇾̣ 𝒳

    open Coalg ᵇ public

    field
      r∘η : {α : T}{Γ Δ : Ctx}{v : ℐ α Γ}{ρ : Γ ↝ Δ}
          → r (η v) ρ ≡ η (ρ v)

  -- Pointed coalgebra homomorphism
  record Coalgₚ⇒  {𝒳 𝒴 : Familyₛ}(𝒳ᴮ : Coalgₚ 𝒳)(𝒴ᴮ : Coalgₚ 𝒴)
                  (f : 𝒳 ⇾̣ 𝒴) : Set where
    private module 𝒳 = Coalgₚ 𝒳ᴮ
    private module 𝒴 = Coalgₚ 𝒴ᴮ
    field
      ᵇ⇒ : Coalg⇒ 𝒳.ᵇ 𝒴.ᵇ f
      ⟨η⟩ : {α : T}{Γ : Ctx}{v : ℐ α Γ}
          → f (𝒳.η v) ≡ 𝒴.η v

    open Coalg⇒ ᵇ⇒ public

  -- Pointed coalgebra of variables
  ℐᵇ : Coalg ℐ
  ℐᵇ = record { r = λ v ρ → ρ v ; counit = refl ; comult = refl }

  ℐᴮ : Coalgₚ ℐ
  ℐᴮ = record { ᵇ = ℐᵇ ; η = id ; r∘η = refl }

  -- □ 𝒳 is free pointed coalgebra on pointed families
  □ᴮ : (𝒳 : Familyₛ) → ℐ ⇾̣ 𝒳 → Coalgₚ (□ 𝒳)
  □ᴮ 𝒳 η = record { ᵇ = □ᵇ 𝒳 ; η = λ v ρ → η (ρ v) ; r∘η = refl }

  -- Renaming map is a homomorphism
  rᵇ⇒ : {𝒳 : Familyₛ}{𝒳ᵇ : Coalg 𝒳} → Coalg⇒ 𝒳ᵇ (□ᵇ 𝒳) (Coalg.r 𝒳ᵇ)
  rᵇ⇒ {𝒳}{𝒳ᵇ} = record { ⟨r⟩ = λ{ {ρ = ρ}{t} → dext λ ϱ → sym (Coalg.comult 𝒳ᵇ) } }

  -- Identity and point are homomorphisms
  idᴮ⇒ : {𝒳 : Familyₛ}{𝒳ᴮ : Coalgₚ 𝒳} → Coalgₚ⇒ 𝒳ᴮ 𝒳ᴮ id
  idᴮ⇒ = record { ᵇ⇒ = record { ⟨r⟩ = refl } ; ⟨η⟩ = refl }

  ηᴮ⇒ : {𝒳 : Familyₛ}(𝒳ᴮ : Coalgₚ 𝒳) → Coalgₚ⇒ ℐᴮ 𝒳ᴮ (Coalgₚ.η 𝒳ᴮ)
  ηᴮ⇒ 𝒳ᴮ = record { ᵇ⇒ = record { ⟨r⟩ = sym (Coalgₚ.r∘η 𝒳ᴮ) } ; ⟨η⟩ = refl }
