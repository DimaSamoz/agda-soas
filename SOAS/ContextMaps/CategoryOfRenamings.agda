-- {-# OPTIONS --rewriting #-}

-- The category of contexts and renamings
module SOAS.ContextMaps.CategoryOfRenamings {T : Set} where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Variable
open import SOAS.ContextMaps.Combinators (ℐ {T})

open import Categories.Functor.Bifunctor
open import Categories.Object.Initial
open import Categories.Object.Coproduct
open import Categories.Category.Cocartesian

import Categories.Morphism


-- The category of contexts and renamings, defined as the Lawvere theory
-- associated with the clone of variables. In elementary terms it has
-- contexts Γ, Δ as objects, and renamings Γ ↝ Δ ≜ Γ ~[ ℐ → ℐ ]↝ Δ as arrows.
𝔽 : Category 0ℓ 0ℓ 0ℓ
𝔽 = categoryHelper (record
  { Obj = Ctx
  ; _⇒_ = _↝_
  ; _≈_ = λ {Γ} ρ₁ ρ₂ → ∀{α : T}{v : ℐ α Γ} → ρ₁ v ≡ ρ₂ v
  ; id = λ x → x
  ; _∘_ = λ ϱ ρ v → ϱ (ρ v)
  ; assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; equiv = record { refl = refl ; sym = λ p → sym p ; trans = λ p q → trans p q }
  ; ∘-resp-≈ = λ{ {f = ρ₁} p₁ p₂ → trans (cong ρ₁ p₂) p₁ }
  })

module 𝔽 = Category 𝔽 using (op) renaming ( _∘_      to _∘ᵣ_
                                          ; _≈_      to _≈ᵣ_
                                          ; id       to idᵣ
                                          ; ∘-resp-≈ to ∘-resp-≈ᵣ )
open 𝔽 public

id′ᵣ : (Γ : Ctx) → Γ ↝ Γ
id′ᵣ Γ = idᵣ {Γ}

-- Category of context is co-Cartesian, given by the empty initial context and
-- context concatenation as the monoidal product.
𝔽:Cocartesian : Cocartesian 𝔽
𝔽:Cocartesian = record
  { initial = record
    { ⊥ = ∅
    ; ⊥-is-initial = record { ! = λ{()} ; !-unique = λ{ f {_} {()}} }
    }
  ; coproducts = record { coproduct = λ {Γ}{Δ} → record
    { A+B = Γ ∔ Δ
    ; i₁ = expandʳ Δ
    ; i₂ = expandˡ Γ
    ; [_,_] = copair
    ; inject₁ = λ{ {Θ}{ρ}{ϱ} → i₁-commute ρ ϱ _ }
    ; inject₂ = λ{ {Θ}{ρ}{ϱ} → i₂-commute ρ ϱ _ }
    ; unique = λ{ p₁ p₂ → unique {Γ}{Δ} _ _ _ p₁ p₂ _ }
    } }
  }
  where

  in₁ : (Γ Δ : Ctx) → Γ ↝ Γ ∔ Δ
  in₁ (α ∙ Γ) Δ new     = new
  in₁ (α ∙ Γ) Δ (old v) = old (in₁ Γ Δ v)

  in₂ : (Γ Δ : Ctx) → Δ ↝ Γ ∔ Δ
  in₂ ∅       Δ v = v
  in₂ (α ∙ Γ) Δ v = old (in₂ Γ Δ v)

  i₁-commute : {Γ Δ Θ : Ctx}{α : T}(ρ : Γ ↝ Θ)(ϱ : Δ ↝ Θ)(v : ℐ α Γ)
             → copair ρ ϱ (expandʳ Δ v) ≡ ρ v
  i₁-commute ρ ϱ new = refl
  i₁-commute ρ ϱ (old v) = i₁-commute (ρ ∘ old) ϱ v

  i₂-commute : {Γ Δ Θ : Ctx}{α : T}(ρ : Γ ↝ Θ)(ϱ : Δ ↝ Θ)(v : ℐ α Δ)
             → copair ρ ϱ (expandˡ Γ v) ≡ ϱ v
  i₂-commute {∅} ρ ϱ v = refl
  i₂-commute {α ∙ Γ} ρ ϱ v = i₂-commute (ρ ∘ old) ϱ v

  unique : {Γ Δ Θ : Ctx}{α : T}(ρ : Γ ↝ Θ)(ϱ : Δ ↝ Θ)(π : Γ ∔ Δ ↝ Θ)
         → (π ∘ᵣ expandʳ Δ ≈ᵣ ρ)
         → (π ∘ᵣ expandˡ Γ ≈ᵣ ϱ)
         → (v : ℐ α (Γ ∔ Δ)) → copair ρ ϱ v ≡ π v
  unique {∅} ρ ϱ π p₁ p₂ v = sym p₂
  unique {α ∙ Γ} ρ ϱ π p₁ p₂ new = sym p₁
  unique {α ∙ Γ} ρ ϱ π p₁ p₂ (old v) = unique (ρ ∘ old) ϱ (π ∘ old) p₁ p₂ v


module 𝔽:Co = Cocartesian 𝔽:Cocartesian
module ∔ = BinaryCoproducts (Cocartesian.coproducts 𝔽:Cocartesian)

-- | Special operations coming from the coproduct structure

-- Concatenation is a bifunctor
∔:Bifunctor : Bifunctor 𝔽 𝔽 𝔽
∔:Bifunctor = 𝔽:Co.-+-

-- Left context concatenation functor Γ ∔ (-) : 𝔽 ⟶ 𝔽, for any context Γ
_∔F– : Ctx → Functor 𝔽 𝔽
Γ ∔F– = Γ ∔.+-

-- Right context concatenation functor (-) ∔ Δ : 𝔽 ⟶ 𝔽, for any context Δ
–∔F_ : Ctx → Functor 𝔽 𝔽
–∔F Δ  = ∔.-+ Δ

-- Functorial mapping and injections
_∣∔∣_ : {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx}(ρ : Γ₁ ↝ Γ₂)(ϱ : Δ₁ ↝ Δ₂) → (Γ₁ ∔ Δ₁) ↝ (Γ₂ ∔ Δ₂)
_∣∔∣_ = ∔._+₁_

_∣∔_ : {Γ₁ Γ₂ : Ctx}(ρ : Γ₁ ↝ Γ₂)(Δ : Ctx) → (Γ₁ ∔ Δ) ↝ (Γ₂ ∔ Δ)
ρ ∣∔ Δ = ρ ∣∔∣ id′ᵣ Δ

_∔∣_ : {Δ₁ Δ₂ : Ctx}(Γ : Ctx)(ϱ : Δ₁ ↝ Δ₂) → (Γ ∔ Δ₁) ↝ (Γ ∔ Δ₂)
Γ ∔∣ ϱ =  id′ᵣ Γ ∣∔∣ ϱ

inl  : (Γ {Δ} : Ctx) → Γ ↝ Γ ∔ Δ
inl Γ {Δ} v = ∔.i₁ {Γ}{Δ} v

inr  : (Γ {Δ} : Ctx) → Δ ↝ Γ ∔ Δ
inr Γ {Δ} v = ∔.i₂ {Γ}{Δ} v


-- Left context concatenation represents weakening a variable in Γ by an
-- arbitrary new context Θ to get a variable in context (Θ ∔ Γ).
module Concatˡ Γ = Functor (Γ ∔F–)
    using () renaming ( F₁           to _∔ᵣ_
                      ; identity     to ∔identity
                      ; homomorphism to ∔homomorphism
                      ; F-resp-≈     to ∔F-resp-≈)
open Concatˡ public

-- Context extension represents weakening by a single type, and it's a special
-- case of context concatenation with a singleton context.
module Ext τ = Functor (⌊ τ ⌋ ∔F–)
    using () renaming ( F₁           to _∙ᵣ_
                      ; identity     to ∙identity
                      ; homomorphism to ∙homomorphism
                      ; F-resp-≈     to ∙F-resp-≈)
open Ext public

-- The two coincide (since add is a special case of copair)
-- but not definitionally: ∙ᵣ is the parallel sum of id : ⌊ τ ⌋ ↝ ⌊ τ ⌋ and ρ : Γ ↝ Δ
-- (i.e. the copairing of expandʳ ⌊ τ ⌋ Δ  : ⌊ τ ⌋ ↝ τ ∙ Δ and old ∘ ρ :  Γ ↝ τ ∙ Δ)
-- while liftᵣ is the copairing of new : ⌊ τ ⌋ ↝ τ ∙ Δ and old ∘ ρ :  Γ ↝ τ ∙ Δ
∙ᵣ-as-add : {α τ : T}{Γ Δ : Ctx} → (ρ : Γ ↝ Δ)(v : ℐ α (τ ∙ Γ))
        → add new (old ∘ ρ) v ≡ (τ ∙ᵣ ρ) v
∙ᵣ-as-add ρ new = refl
∙ᵣ-as-add ρ (old v) = refl

-- Making this a definitional equality simplifies things significantly

-- Right context concatenation is possible but rarely needed.
module Concatʳ Δ =  Functor (–∔F Δ )
