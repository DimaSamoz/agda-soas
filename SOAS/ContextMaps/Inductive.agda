
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

infixl 40 _◂_

infix 50 _⟩
pattern _⟩ t  = t ◂ •

-- Functorial mapping
Sub₁ : (f : 𝒳 ⇾̣ 𝒴) → Sub 𝒳 Γ Δ → Sub 𝒴 Γ Δ
Sub₁ f • = •
Sub₁ f (x ◂ σ) = f x ◂ Sub₁ f σ

-- Conversion between inductive substitutions and context maps
module _ {𝒳 : Familyₛ} where
  lookup : Sub 𝒳 Γ Δ → Γ ~[ 𝒳 ]↝ Δ
  lookup • ()
  lookup (t ◂ σ) new = t
  lookup (t ◂ σ) (old v) = lookup σ v

  tabulate : Γ ~[ 𝒳 ]↝ Δ → Sub 𝒳 Γ Δ
  tabulate {Γ = ∅} σ = •
  tabulate {Γ = α ∙ Γ} σ = σ new ◂ tabulate (σ ∘ old)


  lu∘tab≈id : (σ : Γ ~[ 𝒳 ]↝ Δ) (v : ℐ α Γ)
         → lookup (tabulate σ) v ≡ σ v
  lu∘tab≈id {Γ = α ∙ Γ} σ new = refl
  lu∘tab≈id {Γ = α ∙ Γ} σ (old v) = lu∘tab≈id (σ ∘ old) v

  tab∘lu≈id : (σ : Sub 𝒳 Γ Δ) → tabulate (lookup σ) ≡ σ
  tab∘lu≈id • = refl
  tab∘lu≈id (x ◂ σ) rewrite tab∘lu≈id σ = refl

-- Naturality conditions
tabulate-nat : (f : 𝒳 ⇾̣ 𝒴)(σ : Γ ~[ 𝒳 ]↝ Δ)
          → tabulate {𝒴} (f ∘ σ) ≡ Sub₁ f (tabulate {𝒳} σ)
tabulate-nat {Γ = ∅} f σ = refl
tabulate-nat {Γ = α ∙ Γ} f σ = cong (f (σ new) ◂_) (tabulate-nat f (σ ∘ old))

lookup-nat : (f : 𝒳 ⇾̣ 𝒴)(σ : Sub 𝒳 Γ Δ)(v : ℐ α Γ)
          → lookup (Sub₁ f σ) v ≡ f (lookup σ v)
lookup-nat f (x ◂ σ) new     = refl
lookup-nat f (x ◂ σ) (old v) = lookup-nat f σ v
