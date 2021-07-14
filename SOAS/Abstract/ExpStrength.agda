
-- Exponential and compatible strengths
module SOAS.Abstract.ExpStrength {T : Set} where

open import SOAS.Families.Core {T}
open import SOAS.Context
open import SOAS.Variable
open import SOAS.ContextMaps.Combinators
open import SOAS.ContextMaps.CategoryOfRenamings

open import SOAS.Common
open import SOAS.Coalgebraic.Strength
import SOAS.Abstract.Coalgebra as →□
open →□.Sorted
open →□.Unsorted using (⊤ᵇ) renaming (Coalg to UCoalg ; Coalg⇒ to UCoalg⇒ ; □ᵇ to □ᵘᵇ)
import SOAS.Abstract.Box as □ ; open □.Sorted

open import SOAS.Families.BCCC using (⊤ₘ)

private
  variable
    X : Family
    𝒴 𝒵 : Familyₛ
    Γ Δ Θ : Ctx
    α : T

-- Mixed-sorted Cartesian and linear exponentials
_⇨_ : Family → Familyₛ → Familyₛ
(X ⇨ 𝒴) τ Γ =  X Γ → 𝒴 τ Γ

_➡_ : Family → Familyₛ → Familyₛ
X ➡ 𝒴 = □ (X ⇨ 𝒴)

_⊸_ : Family → Familyₛ → Familyₛ
(X ⊸ 𝒴) α Γ = {Δ : Ctx} → X Δ → 𝒴 α (Γ ∔ Δ)

[_⊸_] : Familyₛ → Familyₛ → Family
[ 𝒳 ⊸ 𝒴 ] Γ = {τ : T}{Δ : Ctx} → 𝒳 τ Δ → 𝒴 τ (Δ ∔ Γ)

-- Linear exponential [ 𝒳 ⊸ 𝒴 ] is an unsorted coalgebra if 𝒴 is sorted coalgebra
[_⊸_]ᵇ : (𝒳 {𝒴} : Familyₛ) → Coalg 𝒴 → UCoalg ([ 𝒳 ⊸ 𝒴 ])
[ 𝒳 ⊸ 𝒴ᵇ ]ᵇ = record
  { r = λ l ρ {_}{Δ} x → r (l x) (Δ ∔∣ ρ)
  ; counit = λ{ {Γ = Γ}{t = l} → iext (dext λ {Δ} ρ →  trans (r≈₂ (Concatʳ.identity Γ {Δ})) counit) }
  ; comult = λ{ {Γ = Γ}{Δ}{Θ}{ρ = ρ}{ϱ}{l} → iext (dext λ {Ξ} x → trans (r≈₂ (Functor.homomorphism (Ξ ∔F–))) comult) } }
  where
  open Coalg 𝒴ᵇ

-- Shorthands
⟅_⇨_⟆ : Familyₛ → Familyₛ → Familyₛ
⟅ 𝒳 ⇨ 𝒴 ⟆ = [ 𝒳 ⊸ 𝒴 ] ⇨ 𝒴
⟅_➡_⟆ : Familyₛ → Familyₛ → Familyₛ
⟅ 𝒳 ➡ 𝒴 ⟆ = [ 𝒳 ⊸ 𝒴 ] ➡ 𝒴
⟅_⊸_⟆ : Familyₛ → Familyₛ → Familyₛ
⟅ 𝒳 ⊸ 𝒴 ⟆ = [ 𝒳 ⊸ 𝒴 ] ⊸ 𝒴

-- Exponential strength of an endofunctor
record ExpStrength (Fᶠ : Functor 𝔽amiliesₛ 𝔽amiliesₛ) : Set₁ where
  open Functor Fᶠ

  field
    -- Strength transformation that lifts a 𝒫-substitution over an endofunctor F₀
    estr : {X : Family}(Xᵇ : UCoalg X)(𝒴 : Familyₛ)
         → F₀ (X ⇨ 𝒴) ⇾̣ (X ⇨ F₀ 𝒴)

    -- Naturality conditions for the two components
    estr-nat₁ : {X X′ : Family}{Xᵇ : UCoalg X}{X′ᵇ : UCoalg X′}{𝒴 : Familyₛ}
              → {f : X′ ⇾ X}(fᵇ⇒ : UCoalg⇒ X′ᵇ Xᵇ f)
              → (e : F₀ (X ⇨ 𝒴) α Γ) (x : X′ Γ)
      → estr Xᵇ 𝒴 e (f x)
      ≡ estr X′ᵇ 𝒴 (F₁ (λ e x → e (f x)) e) x

    estr-nat₂ : {X : Family}{Xᵇ : UCoalg X}{𝒴 𝒴′ : Familyₛ}
              → (g : 𝒴 ⇾̣ 𝒴′)(e : F₀ (X ⇨ 𝒴) α Γ)(x : X Γ)
      → estr Xᵇ 𝒴′ (F₁ (λ e x → g (e x)) e) x
      ≡ F₁ g (estr Xᵇ 𝒴 e x)

    estr-unit : {𝒴 : Familyₛ}{e : F₀ (⊤ₘ ⇨ 𝒴) α Γ}
              → estr ⊤ᵇ 𝒴 e tt ≡ F₁ (λ e′ → e′ tt) e

  -- Derived unit law
  estr-unit′ : {X : Family}{Xᵇ : UCoalg X}{𝒴 : Familyₛ}{e : F₀ (X ⇨ 𝒴) α Γ}
               {x : {Γ : Ctx} → X Γ}(fᵇ⇒ : UCoalg⇒ ⊤ᵇ Xᵇ (λ _ → x))
             → estr Xᵇ 𝒴 e x ≡ F₁ (λ e′ → e′ x) e
  estr-unit′ {X = X}{Xᵇ}{𝒴}{e}{x} fᵇ⇒ = begin
        estr Xᵇ 𝒴 e x                                  ≡⟨⟩
        estr Xᵇ 𝒴 e ((λ _ → x) tt)                     ≡⟨ estr-nat₁ fᵇ⇒ e tt ⟩
        estr ⊤ᵇ 𝒴 (F₁ (λ e′ _ → e′ x) e) tt            ≡⟨ estr-unit ⟩
        F₁ (λ e′ → e′ tt) (F₁ (λ e′ _ → e′ x) e)        ≡˘⟨ homomorphism ⟩
        F₁ (λ e′ → e′ x) e
    ∎ where open ≡-Reasoning

  -- Combination of coalgebraic and exponential strength over X ➡ 𝒴 = □ (X ⇨ 𝒴)
  module ➡-Strength (F:Str : Strength Fᶠ) where
    open Strength F:Str
    open ≡-Reasoning
    □estr : (Xᵇ : UCoalg X)(𝒴 : Familyₛ)
          → F₀ (X ➡ 𝒴) ⇾̣ (X ➡ F₀ 𝒴)
    □estr {X} Xᵇ 𝒴 e ρ x = estr Xᵇ 𝒴 (str ℐᴮ (X ⇨ 𝒴) e ρ) x

-- Compatible exponential and coalgebraic strengths
-- (for now no extra condition)
record CompatStrengths (Fᶠ : Functor 𝔽amiliesₛ 𝔽amiliesₛ) : Set₁ where
  open Functor Fᶠ
  field
    CoalgStr : Strength Fᶠ
    ExpStr : ExpStrength Fᶠ

  open Strength CoalgStr public
  open ExpStrength ExpStr public

  open ➡-Strength CoalgStr public
