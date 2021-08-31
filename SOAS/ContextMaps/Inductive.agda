
-- Inductively constructed substitution maps
module SOAS.ContextMaps.Inductive {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Sorting
open import SOAS.Families.Core {T}
open import SOAS.Variable

private
  variable
    α : T
    Γ Δ : Ctx
    𝒳 𝒴 : Familyₛ

-- A list of terms in context Δ for every variable in context Γ
data Sub (𝒳 : Familyₛ) : Ctx → Ctx → Set where
  •   : Sub 𝒳 ∅ Δ
  _◂_ : 𝒳 α Δ → Sub 𝒳 Γ Δ → Sub 𝒳 (α ∙ Γ) Δ

infixl 120 _◂_

infix 150 _⟩
pattern _⟩ t  = t ◂ •

-- Functorial mapping
Sub₁ : (f : 𝒳 ⇾̣ 𝒴) → Sub 𝒳 Γ Δ → Sub 𝒴 Γ Δ
Sub₁ f • = •
Sub₁ f (x ◂ σ) = f x ◂ Sub₁ f σ

-- Conversion between inductive substitutions and context maps
module _ {𝒳 : Familyₛ} where
  index : Sub 𝒳 Γ Δ → Γ ~[ 𝒳 ]↝ Δ
  index • ()
  index (t ◂ σ) new = t
  index (t ◂ σ) (old v) = index σ v

  tabulate : Γ ~[ 𝒳 ]↝ Δ → Sub 𝒳 Γ Δ
  tabulate {Γ = ∅} σ = •
  tabulate {Γ = α ∙ Γ} σ = σ new ◂ tabulate (σ ∘ old)


  ix∘tab≈id : (σ : Γ ~[ 𝒳 ]↝ Δ) (v : ℐ α Γ)
         → index (tabulate σ) v ≡ σ v
  ix∘tab≈id {Γ = α ∙ Γ} σ new = refl
  ix∘tab≈id {Γ = α ∙ Γ} σ (old v) = ix∘tab≈id (σ ∘ old) v

  tab∘ix≈id : (σ : Sub 𝒳 Γ Δ) → tabulate (index σ) ≡ σ
  tab∘ix≈id • = refl
  tab∘ix≈id (x ◂ σ) rewrite tab∘ix≈id σ = refl

-- Naturality conditions
tabulate-nat : (f : 𝒳 ⇾̣ 𝒴)(σ : Γ ~[ 𝒳 ]↝ Δ)
          → tabulate {𝒴} (f ∘ σ) ≡ Sub₁ f (tabulate {𝒳} σ)
tabulate-nat {Γ = ∅} f σ = refl
tabulate-nat {Γ = α ∙ Γ} f σ = cong (f (σ new) ◂_) (tabulate-nat f (σ ∘ old))

index-nat : (f : 𝒳 ⇾̣ 𝒴)(σ : Sub 𝒳 Γ Δ)(v : ℐ α Γ)
          → index (Sub₁ f σ) v ≡ f (index σ v)
index-nat f (x ◂ σ) new     = refl
index-nat f (x ◂ σ) (old v) = index-nat f σ v
