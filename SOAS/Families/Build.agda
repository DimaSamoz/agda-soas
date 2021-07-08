
-- Operators for combining and building families
module SOAS.Families.Build {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Sorting {T}
open import SOAS.Families {T}

-- Generalised sums and pattern matching
data +₂ (A B : Set) : Set where
  _₁ : A → +₂ A B
  _₂ : B → +₂ A B

data +₃ (A B C : Set) : Set where
  _₁ : A → +₃ A B C
  _₂ : B → +₃ A B C
  _₃ : C → +₃ A B C

data +₄ (A B C D : Set) : Set where
  _₁ : A → +₄ A B C D
  _₂ : B → +₄ A B C D
  _₃ : C → +₄ A B C D
  _₄ : D → +₄ A B C D

infixr 60 _₁
infixr 60 _₂
infixr 60 _₃
infixr 60 _₄

₂| : {A B : Set}{X : Set} → (A → X) → (B → X) → (+₂ A B → X)
₂| f g (a ₁) = f a
₂| f g (b ₂) = g b

₃| : {A B C : Set}{X : Set} → (A → X) → (B → X) → (C → X) → (+₃ A B C → X)
₃| f g h (a ₁) = f a
₃| f g h (b ₂) = g b
₃| f g h (c ₃) = h c

₄| : {A B C D : Set}{X : Set} → (A → X) → (B → X) → (C → X) → (D → X) → (+₄ A B C D → X)
₄| f g h e (a ₁) = f a
₄| f g h e (b ₂) = g b
₄| f g h e (c ₃) = h c
₄| f g h e (d ₄) = e d


pattern _ₛ 𝔪 = 𝔪 ₁
pattern _ₘ 𝔪 = 𝔪 ₂
infixr 60 _ₛ
infixr 60 _ₘ

-- Empty and unit families

data Ø : Familyₛ where

data _⊩_ (Γ : Ctx)(α : T) : Familyₛ where
  ● : (Γ ⊩ α) α Γ

⊩_ : T → Familyₛ
⊩ α = ∅ ⊩ α

infix 20 _⊩_
infix 20 ⊩_


-- Sum of families

infix 10 _⊹_
infix 10 _⊹_⊹_
infix 10 _⊹_⊹_⊹_

_⊹_ : Familyₛ → Familyₛ → Familyₛ
(𝒳 ⊹ 𝒴) α Γ = +₂ (𝒳 α Γ) (𝒴 α Γ)

_⊹₁_ : {𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ : Familyₛ} → (𝒳₁ ⇾̣ 𝒳₂) → (𝒴₁ ⇾̣ 𝒴₂)
     → (𝒳₁ ⊹ 𝒴₁) ⇾̣ (𝒳₂ ⊹ 𝒴₂)
(f ⊹₁ g) (x ₁) = (f x) ₁
(f ⊹₁ g) (y ₂) = (g y) ₂

_⊹_⊹_ : Familyₛ → Familyₛ → Familyₛ → Familyₛ
(𝒳 ⊹ 𝒴 ⊹ 𝒵) α Γ = +₃ (𝒳 α Γ) (𝒴 α Γ) (𝒵 α Γ)

_⊹_⊹_⊹_ : Familyₛ → Familyₛ → Familyₛ → Familyₛ → Familyₛ
(𝒳 ⊹ 𝒴 ⊹ 𝒵 ⊹ 𝒲) α Γ = +₄ (𝒳 α Γ) (𝒴 α Γ) (𝒵 α Γ) (𝒲 α Γ)


-- | Metavariable contexts

-- Inductive construction of context- and type-indexed sets
data MCtx : Set where
  ◾     : MCtx
  _⊩_≀_ : (Π : Ctx {T}) → (τ : T) → MCtx → MCtx

-- Pattern synonym for parameterless elements and final elements
infixr 20 _⊩_≀_
infixr 20 ⊩_≀_
infixr 25 _⊪_
infixr 25 ⊪_
pattern ⊩_≀_ τ 𝔐 = ∅ ⊩ τ ≀ 𝔐
pattern _⊪_ Π τ = Π ⊩ τ ≀ ◾
pattern ⊪_ τ = ∅ ⊩ τ ≀ ◾

private
  variable
    Γ Δ Θ Π : Ctx
    α β γ τ : T
    𝔐 : MCtx

-- Membership of metavariable contexts
data _⊩_∈_ : Ctx → T → MCtx → Set where
  ↓ : Π ⊩ τ ∈ (Π ⊩ τ ≀ 𝔐)
  ↑_ : Π ⊩ τ ∈ 𝔐 → Π ⊩ τ ∈ (Γ ⊩ α ≀ 𝔐)

infixr 80 ↑_

-- Metavariable context can be interpreted as a family via the membership
∥_∥ : MCtx → Familyₛ
∥ 𝔐 ∥ α Γ = Γ ⊩ α ∈ 𝔐
infixr 60 ∥_∥

_▷_ : MCtx → (Familyₛ → Familyₛ) → Familyₛ
𝔐 ▷ 𝒳 = 𝒳 ∥ 𝔐 ∥

-- Metavariable de Bruijn indices
pattern 𝔞 = ↓
pattern 𝔟 = ↑ ↓
pattern 𝔠 = ↑ ↑ ↓
pattern 𝔡 = ↑ ↑ ↑ ↓
pattern 𝔢 = ↑ ↑ ↑ ↑ ↓
pattern 𝔣 = ↑ ↑ ↑ ↑ ↑ ↓

pattern 𝔞ₘ = ↓ ₘ
pattern 𝔟ₘ = ↑ ↓ ₘ
pattern 𝔠ₘ = ↑ ↑ ↓ ₘ
pattern 𝔡ₘ = ↑ ↑ ↑ ↓ ₘ
pattern 𝔢ₘ = ↑ ↑ ↑ ↑ ↓ ₘ
pattern 𝔣ₘ = ↑ ↑ ↑ ↑ ↑ ↓ ₘ
