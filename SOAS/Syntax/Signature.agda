
-- Binding signatures
module SOAS.Syntax.Signature (T : Set) where

open import SOAS.Syntax.Arguments {T}

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable

open import SOAS.Families.Core {T}
open import SOAS.Families.BCCC {T} using (⊤ₘ)

open import SOAS.Coalgebraic.Strength
open import SOAS.Coalgebraic.Lift
open import SOAS.Coalgebraic.Map

open import SOAS.Abstract.Hom

open import SOAS.Abstract.ExpStrength
import SOAS.Abstract.Coalgebra as →□
open →□.Sorted
open →□.Unsorted renaming (Coalg to UCoalg ; Coalg⇒ to UCoalg⇒)

open import Data.List.Base using ([] ; _∷_ ; List)

private
  variable
    Γ Δ Θ : Ctx
    α τ : T

-- Binding signature for a second-order syntax, consisting of a set of operators
-- O and an arity assignment ∣_∣
record Signature (O : Set) : Set₁ where
  constructor sig
  field ∣_∣ : O → List (Ctx × T) × T

  -- Sort and arity of an operator
  Sort : O → T
  Sort o = proj₂ ∣ o ∣

  Arity : O → List (Ctx × T)
  Arity o = proj₁ ∣ o ∣

  -- Signature endofunctor
  ⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ
  ⅀F  = record
    { F₀ = λ 𝒳 α Γ → Σ[ o ∈ O ] (α ≡ Sort o × Arg (Arity o) 𝒳 Γ)
    ; F₁ = λ{ f (o , e , ar) → o , e , (F₁ o f ar)}
    ; identity = λ{ {x = o , e , ar} → cong (λ - → o , e , -) (identity o) }
    ; homomorphism = λ{ {x = o , e , ar} → cong (λ - → o , e , -) (homomorphism o) }
    ; F-resp-≈ = λ{ p {x = o , e , ar} → cong (λ - → o , e , -) (F-resp-≈ o p) }
    } where open module AF o =  Functor (ArgF (Arity o))

  pattern _⋮_ o ar = (o , refl , ar)
  infix 1 _⋮_

  open import SOAS.Metatheory.Algebra {T} ⅀F public

  -- Coalgebraic and exponential strength for signature endofunctor
  private
    str : {𝒫 : Familyₛ}(𝒫ᴮ : Coalgₚ 𝒫)(𝒳 : Familyₛ)
          (as : List (Ctx × T))(σ : Γ ~[ 𝒫 ]↝ Δ)
        → Arg as 〖 𝒫 , 𝒳 〗 Γ → Arg as 𝒳 Δ
    str 𝒫ᴮ 𝒳 [] σ x = tt
    str 𝒫ᴮ 𝒳 ((Θ , τ) ∷ []) σ h = h (lift 𝒫ᴮ Θ σ)
    str 𝒫ᴮ 𝒳 ((Θ , τ) ∷ a ∷ as) σ (h , at) = h (lift 𝒫ᴮ Θ σ) , str 𝒫ᴮ 𝒳 (a ∷ as) σ at

    str-nat₁ : {𝒫 𝒬 𝒳 : Familyₛ} {𝒫ᴮ : Coalgₚ 𝒫} {𝒬ᴮ : Coalgₚ 𝒬}
             → {f : 𝒬 ⇾̣ 𝒫} (fᴮ⇒ : Coalgₚ⇒ 𝒬ᴮ 𝒫ᴮ f)
             → (as : List (Ctx × T))
             → (h : Arg as 〖 𝒫 , 𝒳 〗 Γ) (σ : Γ ~[ 𝒬 ]↝ Δ)
             → str 𝒫ᴮ 𝒳 as (λ x → f (σ x)) h
             ≡ str 𝒬ᴮ 𝒳 as σ (Arg₁ as (λ{ h′ ς → h′ (λ v → f (ς v))}) h)
    str-nat₁ fᴮ⇒ [] h σ = refl
    str-nat₁ {𝒳 = 𝒳} fᴮ⇒ ((Θ , τ) ∷ []) h σ = lift-comp 𝒳 Θ fᴮ⇒ h σ
    str-nat₁ {𝒳 = 𝒳} fᴮ⇒ ((Θ , τ) ∷ a ∷ as) (h , ap) σ =
      cong₂ _,_ (lift-comp 𝒳 Θ fᴮ⇒ h σ) (str-nat₁ fᴮ⇒ (a ∷ as) ap σ)

    str-nat₂ : {𝒫 𝒳 𝒴 : Familyₛ} {𝒫ᴮ : Coalgₚ 𝒫}
             → (f : 𝒳 ⇾̣ 𝒴)
             → (as : List (Ctx × T))
             → (h : Arg as 〖 𝒫 , 𝒳 〗 Γ) (σ : Γ ~[ 𝒫 ]↝ Δ)
             → str 𝒫ᴮ 𝒴 as σ (Arg₁ as (λ{ h′ ς → f (h′ ς)}) h)
             ≡ Arg₁ as f (str 𝒫ᴮ 𝒳 as σ h)
    str-nat₂ f [] h σ = refl
    str-nat₂ f ((Θ , τ) ∷ []) h σ = refl
    str-nat₂ f ((Θ , τ) ∷ a ∷ as) (h , ap) σ = cong (_ ,_) (str-nat₂ f (a ∷ as) ap σ)

    str-unit : (𝒳 : Familyₛ)
             → (as : List (Ctx × T))
             → (h : Arg as 〖 ℐ , 𝒳 〗 Γ)
             → str ℐᴮ 𝒳 as id h
             ≡ Arg₁ as (λ b → b id) h
    str-unit 𝒳 [] h = refl
    str-unit 𝒳 ((Θ , τ) ∷ []) h = rlift-id 𝒳 Θ h
    str-unit 𝒳 ((Θ , τ) ∷ a ∷ as) (h , ap) = cong₂ _,_ (rlift-id 𝒳 Θ h) (str-unit 𝒳 (a ∷ as) ap)

    str-assoc : (𝒳 : Familyₛ) {𝒫 𝒬 ℛ : Familyₛ}
                {𝒫ᴮ : Coalgₚ 𝒫} {𝒬ᴮ : Coalgₚ 𝒬} {ℛᴮ : Coalgₚ ℛ}
              → {f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗} (fᶜ : Coalgebraic 𝒫ᴮ 𝒬ᴮ ℛᴮ f)
              → (open Coalgebraic fᶜ)
              → (as : List (Ctx × T))
              → (h : Arg as 〖 ℛ , 𝒳 〗 Γ) (σ : Γ ~[ 𝒫 ]↝ Δ) (ς : Δ ~[ 𝒬 ]↝ Θ)
              → str ℛᴮ 𝒳 as (λ v → f (σ v) ς) h
              ≡ str 𝒬ᴮ 𝒳 as ς (str 〖𝒫,𝒴〗ᴮ 〖 𝒬 , 𝒳 〗 as (f ∘ σ) (Arg₁ as (λ{ h ς σ → h (λ v → ς v σ)}) h))
    str-assoc 𝒳 fᶜ [] h σ ς = refl
    str-assoc 𝒳 fᶜ ((Ξ , τ) ∷ []) h σ ς = lift-assoc 𝒳 Ξ fᶜ h σ ς
    str-assoc 𝒳 fᶜ ((Ξ , τ) ∷ a ∷ as) (h , ap) σ ς = cong₂ _,_ (lift-assoc 𝒳 Ξ fᶜ h σ ς) (str-assoc 𝒳 fᶜ (a ∷ as) ap σ ς)

    estr : {X : Family}(Xᵇ : UCoalg X)(𝒴 : Familyₛ)
          (as : List (Ctx × T))
        → Arg as (X ⇨ 𝒴) Γ → (x : X Γ) → Arg as 𝒴 Γ
    estr Xᵇ 𝒴 [] at x = tt
    estr Xᵇ 𝒴 ((Θ , τ) ∷ []) e x = e (UCoalg.wkr Xᵇ Θ x)
    estr Xᵇ 𝒴 ((Θ , τ) ∷ a ∷ as) (e , at) x = (e (UCoalg.wkr Xᵇ Θ x)) , estr Xᵇ 𝒴 (a ∷ as) at x

    estr-nat₁ : {X X′ : Family} {Xᵇ : UCoalg X}
      {X′ᵇ : UCoalg X′} {𝒴 : Familyₛ} {f : X′ ⇾ X} →
      UCoalg⇒ X′ᵇ Xᵇ f →
      (as : List (Ctx × T))
      (h : Arg as (X ⇨ 𝒴) Γ)(x : X′ Γ)
      → estr Xᵇ 𝒴 as h (f x)
      ≡ estr X′ᵇ 𝒴 as (Arg₁ as (λ e x₁ → e (f x₁)) h) x
    estr-nat₁ fᵇ⇒ [] h x = refl
    estr-nat₁ fᵇ⇒ ((Θ , τ) ∷ []) h x = cong h (sym (UCoalg⇒.⟨r⟩ fᵇ⇒))
    estr-nat₁ fᵇ⇒ ((Θ , τ) ∷ a ∷ as) (h , at) x = cong₂ _,_ (cong h (sym (UCoalg⇒.⟨r⟩ fᵇ⇒))) (estr-nat₁ fᵇ⇒ (a ∷ as) at x)

    estr-nat₂ : {X : Family} {Xᵇ : UCoalg X}
        {𝒴 𝒴′ : Familyₛ} (g : 𝒴 ⇾̣ 𝒴′) (as : List (Ctx × T))(at : Arg as (X ⇨ 𝒴) Γ) (x : X Γ)
        → estr Xᵇ 𝒴′ as (Arg₁ as (λ e x → g (e x)) at) x
        ≡ Arg₁ as g (estr Xᵇ 𝒴 as at x)
    estr-nat₂ g [] at x = refl
    estr-nat₂ g ((Θ , τ) ∷ []) h x = refl
    estr-nat₂ g ((Θ , τ) ∷ a ∷ as) (h , at) x = cong (_ ,_) (estr-nat₂ g (a ∷ as) at x)

    estr-unit : {𝒴 : Familyₛ} (as : List (Ctx × T)) {at : Arg as (⊤ₘ ⇨ 𝒴) Γ}
        → estr ⊤ᵇ 𝒴 as at tt ≡ Arg₁ as (λ e′ → e′ tt) at
    estr-unit [] = refl
    estr-unit ((Θ , τ) ∷ []) = refl
    estr-unit ((Θ , τ) ∷ a ∷ as) = cong (_ ,_) (estr-unit (a ∷ as))

  -- Compatible strengths for the signature endofunctor
  ⅀:CompatStr : CompatStrengths ⅀F
  ⅀:CompatStr = record
    { CoalgStr = record
      { str = λ{ 𝒫ᴮ 𝒳 (o , e , ap) σ → o , (e , str 𝒫ᴮ 𝒳 (Arity o) σ ap) }
      ; str-nat₁ = λ{ fᴮ⇒ (o , e , ap) σ → cong (λ - → o , e , -) (str-nat₁ fᴮ⇒ (Arity o) ap σ)}
      ; str-nat₂ = λ{ f (o , e , ap) σ → cong (λ - → o , e , -) (str-nat₂ f (Arity o) ap σ)}
      ; str-unit = λ{ 𝒳 (o , e , ap) → cong (λ - → o , e , -) (str-unit 𝒳 (Arity o) ap)}
      ; str-assoc = λ{ 𝒳 fᶜ (o , e , ap) σ ς → cong (λ - → o , e , -) (str-assoc 𝒳 fᶜ (Arity o) ap σ ς)}
      }
    ; ExpStr = record
      { estr = λ{ Xᵇ 𝒴 (o , refl , at) x → o , refl , estr Xᵇ 𝒴 (Arity o) at x }
      ; estr-nat₁ = λ{ fᵇ⇒ (o , refl , at) x → cong (λ - → o , refl , -) (estr-nat₁ fᵇ⇒ (Arity o) at x)}
      ; estr-nat₂ = λ{ g (o , refl , at) x → cong (λ - → o , refl , -) (estr-nat₂ g (Arity o) at x) }
      ; estr-unit = λ{ {e = (o , refl , at)} → cong (λ - → o , refl , -) (estr-unit (Arity o)) } }
    }
