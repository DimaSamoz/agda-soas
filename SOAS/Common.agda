
-- Common imports and other auxiliary operations used in the library
module SOAS.Common where

open import Categories.Category.Instance.Sets public
open import Axiom.Extensionality.Propositional
  using (Extensionality; ExtensionalityImplicit)
open import Relation.Binary.PropositionalEquality public
  hiding (Extensionality)
  renaming (subst to ≡subst; [_] to ≡[_])

open import Categories.Category public
open import Categories.Category.Helper public
open import Categories.Functor public
  renaming (id to idF)

open import Categories.NaturalTransformation public
  using (ntHelper)
  renaming (NaturalTransformation to NT; id to idN; _∘ᵥ_ to _∘N_)
open import Categories.NaturalTransformation.Equivalence using (_≃_) public
open import Categories.Morphism using (Iso) public

open import Level as L hiding (lift) renaming (suc to lsuc) public
open import Function using (flip; case_of_; _∋_) public renaming (_$_ to _$ᶠ_)
open import Data.Product public using (_×_; proj₁; proj₂; _,_; Σ; module Σ; Σ-syntax; swap)
open import Data.Sum public using (_⊎_ ; inj₁; inj₂)
open import Data.Unit public using (tt)

-- Shorthand for first universe level
1ℓ : Level
1ℓ = lsuc 0ℓ

-- Basic function extensionality postulates
postulate
  -- Extensionality with one explicit or implicit argument
  ext  : Extensionality 0ℓ 0ℓ
  iext : ExtensionalityImplicit 0ℓ 0ℓ

-- Functions with two explicit arguments
ext² : {A : Set} {B : A → Set}{C : (x : A) → B x → Set}
       {f g : (x : A) → (y : B x) → C x y} →
       (∀ x y → f x y ≡ g x y) →
       (λ x y → f x y) ≡ (λ x y → g x y)
ext² p = ext (λ x → ext (λ y → p x y))

-- Functions with one implicit and one explicit argument
dext : {A : Set} {B : A → Set}{C : (x : A) → B x → Set}
       {f g : {x : A} → (y : B x) → C x y} →
       (∀ {x} y → f {x} y ≡ g {x} y) →
       (λ {x} y → f {x} y) ≡ (λ {x} y → g {x} y)
dext p = iext (ext p)

-- Functions with two pairs of implicit-explicit arguments
dext² : {A : Set}{B : A → Set}{C : A → A → Set}
       {D : (x : A) → B x → (y : A) → C x y → Set}
       {f g : {x : A} → (b : B x) → {y : A} → (c : C x y) → D x b y c} →
       (∀ {x} b {y} c → f {x} b {y} c ≡ g {x} b {y} c) →
       (λ {x} b {y} c → f {x} b {y} c) ≡
       (λ {x} b {y} c → g {x} b {y} c)
dext² p = dext (λ {x} y → dext (p {x} y))

-- Functions with one implicit and one explicit argument where the
-- pointwise equality proof does not use the explicit argument
dext′ : {A : Set} {B : A → Set}{C : (x : A) → B x → Set}
       {f g : {x : A} → (y : B x) → C x y} →
       (∀ {x} {y} → f {x} y ≡ g {x} y) →
       (λ {x} y → f {x} y) ≡ (λ {x} y → g {x} y)
dext′ p = dext (λ {x} y → p {x}{y})

-- Use the naming convention for categories
𝕊ets : Category 1ℓ 0ℓ 0ℓ
𝕊ets = Sets 0ℓ
module 𝕊et = Category 𝕊ets

-- Make composition and the identity globally accessible
open Category (Sets 0ℓ) public using (_∘_; id)

-- Set isomorphism shorthands
open import Categories.Morphism 𝕊ets public using ()
        renaming ( _≅_ to _≅ₛ_ ; module ≅ to ≅ₛ ; ≅-setoid to ≅ₛ-setoid)


-- Congruence with the arguments reversed -- easier to focus on the equalities
-- if the congruence environment is very large
congr : ∀{ℓ}{A B : Set ℓ}{x y : A} → x ≡ y → (f : A → B) → f x ≡ f y
congr refl f = refl
