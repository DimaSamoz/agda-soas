
-- Environment model of the STLC
module STLC.Model where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive
open import SOAS.Abstract.Monoid
open import SOAS.Coalgebraic.Lift

open import STLC.Signature
open import STLC.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution Λ:Syn
open import SOAS.Metatheory.SecondOrder.Equality Λ:Syn
open import SOAS.Metatheory.FreeMonoid Λ:Syn
open import SOAS.Syntax.Arguments

open import Data.Nat

private
  variable
    α β γ τ : ΛT
    Γ Δ Π : Ctx
    𝔛 : Familyₛ
Λᴳ : Familyₛ
Λᴳ = Λ Ø

-- Interpretation of types and contexts
⟦_⟧ : ΛT → Set
⟦ N ⟧ = ℕ
⟦ α ↣ β ⟧ = ⟦ α ⟧ → ⟦ β ⟧

⟦_⟧ᶜ : Ctx → Set
⟦ Γ ⟧ᶜ = {α : ΛT} → ℐ α Γ → ⟦ α ⟧

_⁺_ : ⟦ α ⟧ → ⟦ Γ ⟧ᶜ → ⟦ α ∙ Γ ⟧ᶜ
_⁺_ x γ new = x
_⁺_ x γ (old v) = γ v
infixr 10 _⁺_

-- Environment model
Env : Familyₛ
Env α Γ = ⟦ Γ ⟧ᶜ → ⟦ α ⟧

ΣEnvᴹ : ΣMon Env
ΣEnvᴹ = record
  { ᵐ = record
    { η = λ v γ → γ v ; μ = λ t σ δ → t (λ v → σ v δ)
    ; lunit = refl ; runit = refl ; assoc = refl }
  ; 𝑎𝑙𝑔 = λ{ (appₒ ⋮ f , a) γ → f γ (a γ)
          ; (lamₒ ⋮ b) γ → λ a → b (a ⁺ γ) }
  ; μ⟨𝑎𝑙𝑔⟩ = λ{ (appₒ ⋮ _) → refl
             ; (lamₒ ⋮ b) → ext² λ δ a → cong b (dext
                (λ { new → refl ; (old y) → refl })) } }

module Env = FΣM Ø ΣEnvᴹ (λ ())

eval : Λ Ø ⇾̣ Env
eval = Env.𝕖𝕩𝕥
evalᶜ : Λ Ø α ∅ → ⟦ α ⟧
evalᶜ t = eval t (λ ())


_ : evalᶜ {N ↣ N ↣ N} (ƛ ƛ x₁) ≡ λ x y → x
_ = refl

open Theory Ø

-- Operational semantics of the STLC
data Value : Λᴳ α Γ → Set where
  lamⱽ  : {b : Λᴳ β (α ∙ Γ)} →
          Value (ƛ b)

data _⟿_ : Λᴳ α Γ → Λᴳ α Γ → Set where
  ζ-$₁  : {f g : Λᴳ (α ↣ β) Γ}{a : Λᴳ α Γ} →
          f ⟿ g → f $ a ⟿ g $ a
  ζ-$₂  : {f : Λᴳ (α ↣ β) Γ}{a b : Λᴳ α Γ} →
          Value f → a ⟿ b → f $ a ⟿ f $ b
  β-ƛ   : {b : Λᴳ β (α ∙ Γ)}{t : Λᴳ α Γ} →
          Value t → ((ƛ b) $ t) ⟿ [ t /] b

infix 2 _⟿_

-- Evaluation preserves the meaning of terms
sound : {t s : Λᴳ α Γ} → t ⟿ s → (γ : ⟦ Γ ⟧ᶜ) →  eval t γ ≡ eval s γ
sound (ζ-$₁ r) γ rewrite sound r γ = refl
sound (ζ-$₂ _ r) γ rewrite sound r γ = refl
sound (β-ƛ {b = b}{t} x) γ rewrite Env.𝕖𝕩𝕥ᵐ⇒.sub-lemma t b =
  cong (eval b) (dext λ{ new → refl ; (old v) → refl })
