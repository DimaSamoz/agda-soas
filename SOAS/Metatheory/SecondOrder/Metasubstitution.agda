
open import SOAS.Metatheory.Syntax

-- Metasubstitution operation
module SOAS.Metatheory.SecondOrder.Metasubstitution {T : Set}(Syn : Syntax) where

open Syntax Syn

open import SOAS.Metatheory.FreeMonoid Syn

open import SOAS.Common
open import SOAS.Families.Core {T}
open import SOAS.Families.Build
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Construction.Structure as Structure
open import SOAS.ContextMaps.Combinators
open import SOAS.ContextMaps.CategoryOfRenamings

open import SOAS.Abstract.Hom
open import SOAS.Abstract.ExpStrength
import SOAS.Abstract.Coalgebra as →□
open →□.Sorted
import SOAS.Abstract.Box as □ ; open □.Sorted

open import Categories.Monad

open import SOAS.Coalgebraic.Monoid

open import SOAS.Metatheory Syn

private
  variable
    Γ Δ Π : Ctx
    α β τ : T
    𝔛 𝔜 ℨ : Familyₛ
    𝔐 𝔑 : MCtx

open Theory

-- Ground metasubstitution from the monad structure
msub₀ : (𝔛 ⇾̣ 𝕋 𝔜) → 𝕋 𝔛 ⇾̣ 𝕋 𝔜
msub₀ {𝔛}{𝔜} κ t = μ.η 𝔜 (F.₁ κ t) where open Monad ΣMon:Monad

-- Meta-algebra structure on the exponential [ 𝔛 ⊸ 𝒫 ] ⇨ ℳ
[_⊸_]⇨_ᵃ : (𝔛 {𝒫}{ℳ} : Familyₛ) → Coalg 𝒫 → ΣMon ℳ → (𝒫 ⇾̣ ℳ)
         → MetaAlg 𝔛 ([ 𝔛 ⊸ 𝒫 ] ⇨ ℳ)
[_⊸_]⇨_ᵃ 𝔛 {𝒫}{ℳ} 𝒫ᵇ Σℳᵐ ψ = record
  { 𝑎𝑙𝑔 = λ t ζ → ℳ.𝑎𝑙𝑔 (estr [ 𝔛 ⊸ 𝒫ᵇ ]ᵇ ℳ t ζ)
  ; 𝑣𝑎𝑟 = λ v ζ → ℳ.η v
  ; 𝑚𝑣𝑎𝑟 = λ 𝔪 ε ζ → ℳ.μ (ψ (ζ 𝔪)) (copair ℳ (λ x → ε x ζ) ℳ.η)
  } where module ℳ = ΣMon Σℳᵐ

□[_⊸_]⇨_ᵃ : (𝔛 {𝒫}{ℳ} : Familyₛ) → Coalg 𝒫 → ΣMon ℳ → (𝒫 ⇾̣ ℳ)
           → MetaAlg 𝔛 ([ 𝔛 ⊸ 𝒫 ] ➡ ℳ)
□[ 𝔛 ⊸ 𝒫ᵇ ]⇨ Σℳᵐ ᵃ ψ = □ᵃ 𝔛 ([ 𝔛 ⊸ 𝒫ᵇ ]⇨ Σℳᵐ ᵃ ψ)

-- Derived meta-algebra instance for [ 𝔛 ⊸ 𝕋 𝔜 ] ⇨ 𝕋 𝔜
⟅_⇨_⟆ᵃ : (𝔛 𝔜 : Familyₛ) → MetaAlg 𝔛 ⟅ 𝔛 ⇨ 𝕋 𝔜 ⟆
⟅ 𝔛 ⇨ 𝔜 ⟆ᵃ = [ 𝔛 ⊸ 𝕋ᵇ 𝔜 ]⇨ Σ𝕋ᵐ 𝔜 ᵃ id

module MS {𝔛 𝔜 : Familyₛ} =  Semantics 𝔛 ⟅ 𝔛 ⇨ 𝔜 ⟆ᵃ
module □MS {𝔛 𝔜 : Familyₛ} = □Traversal 𝔛 ⟅ 𝔛 ⇨ 𝔜 ⟆ᵃ

-- Metasubstitution operations
-- Base
msub : 𝕋 𝔛 ⇾̣ ⟅ 𝔛 ⇨ 𝕋 𝔜 ⟆
msub = MS.𝕤𝕖𝕞
-- Parametrised
□msub : 𝕋 𝔛 ⇾̣ ⟅ 𝔛 ➡ 𝕋 𝔜 ⟆
□msub = □MS.𝕥𝕣𝕒𝕧
-- Linear
○msub : 𝕋 𝔛 ⇾̣ ⟅ 𝔛 ⊸ 𝕋 𝔜 ⟆
○msub {𝔜 = 𝔜}{Γ = Γ} t ζ = □msub t (inl Γ) λ {_}{Π} 𝔪 → 𝕣𝕖𝕟 𝔜 (ζ 𝔪) (Π ∔∣ inr Γ)

-- Unit parametrisation
□msub-id : (t : 𝕋 𝔛 α Γ)(κ : [ 𝔛 ⊸ 𝕋 𝔜 ] Γ) → □msub t id κ ≡ msub t κ
□msub-id {𝔛}{𝔜 = 𝔜} t κ = cong (λ - → - κ) (□𝕥𝕣𝕒𝕧-id≈𝕤𝕖𝕞 𝔛 ⟅ 𝔛 ⇨ 𝔜 ⟆ᵃ)

-- Unit metasubstitution mapping
ms-unit : [ 𝔛 ⊸ 𝕋 𝔛 ] Γ
ms-unit {𝔛}{Δ = Δ} 𝔪 = 𝕞𝕧𝕒𝕣 𝔛 𝔪 (𝕧𝕒𝕣 𝔛 ∘ inl Δ)

-- | Inductive metasubstitution

-- List of terms in an extended (object variable) context mapped to every element of a metavariable context
data MSub (Γ : Ctx) : MCtx → MCtx → Set₁ where
  ◦   : MSub Γ ◾ 𝔑
  _◃_ : (𝔑 ▷ 𝕋) α (Π ∔ Γ) → MSub Γ 𝔐 𝔑 → MSub Γ (Π ⊩ α ≀ 𝔐) 𝔑

infixr 15 _◃_

-- Application of a metasubstitution to a metavariable
ix≀ : MSub Γ 𝔐 𝔑 → [ ∥ 𝔐 ∥ ⊸ 𝔑 ▷ 𝕋 ] Γ
ix≀ (t ◃ ζ) ↓ = t
ix≀ (t ◃ ζ) (↑ 𝔪) = ix≀ ζ 𝔪

-- Term corresponding to the topmost distinguished metavariable of an extended mvar context
_⊩◌ : (Π : Ctx) → (Π ⊩ β ≀ 𝔐 ▷ 𝕋) β (Π ∔ Γ)
_⊩◌ {β}{𝔐} Π = ms-unit ↓

◌ : (∅ ⊩ β ≀ 𝔐 ▷ 𝕋) β Γ
◌ = ∅ ⊩◌

-- Weakening of metavariable context
wk≀ : (𝔐 ▷ 𝕋) α Γ →  (Π ⊩ τ ≀ 𝔐 ▷ 𝕋) α Γ
wk≀ t = 𝕋₁ ↑_ t

-- Extension of the codomain of a metasubstitution
ext≀ : (Π : Ctx)(τ : T) → MSub Γ 𝔐 𝔑 → MSub Γ 𝔐 (Π ⊩ τ ≀ 𝔑)
ext≀ Π τ ◦ = ◦
ext≀ Π τ (t ◃ κ) = wk≀ t ◃ (ext≀ Π τ κ)

-- Lifting of a metasubstitution
lift≀ : (Π : Ctx)(τ : T) → MSub Γ 𝔐 𝔑 → MSub Γ (Π ⊩ τ ≀ 𝔐) (Π ⊩ τ ≀ 𝔑)
lift≀ Π τ κ = (Π ⊩◌) ◃ (ext≀ Π τ κ)

-- Identity metasubstitution
id≀ : (Γ : Ctx) →  MSub Γ 𝔐 𝔐
id≀ {◾} Γ = ◦
id≀ {Π ⊩ τ ≀ 𝔐} Γ = lift≀ Π τ (id≀ Γ)

-- Left and right weakening of object context of a metasubstitution
inl≀ : MSub Γ 𝔐 𝔑 → MSub (Γ ∔ Δ) 𝔐 𝔑
inl≀ ◦ = ◦
inl≀ {𝔑 = 𝔑} (_◃_ {Π = Π} t κ) = 𝕣𝕖𝕟 ∥ 𝔑 ∥ t (Π ∔∣ inl _) ◃ (inl≀ κ)

inr≀ : (Γ : Ctx) → MSub Δ 𝔐 𝔑 → MSub (Γ ∔ Δ) 𝔐 𝔑
inr≀ _ ◦ = ◦
inr≀ {Δ}{𝔑 = 𝔑} Γ (_◃_ {Π = Π} t κ) = (𝕣𝕖𝕟 ∥ 𝔑 ∥ t (Π ∔∣ inr Γ)) ◃ (inr≀ Γ κ)

-- Application of weakened metasubstitution corresponds to centre weakening
ix-inr≀ : (κ : MSub Δ 𝔐 𝔑)(𝔪 : Π ⊩ τ ∈ 𝔐)
        → ix≀ (inr≀ Γ κ) 𝔪 ≡ (𝕣𝕖𝕟 ∥ 𝔑 ∥ (ix≀ κ 𝔪) (Π ∔∣ inr Γ))
ix-inr≀ (x ◃ κ) ↓ = refl
ix-inr≀ (x ◃ κ) (↑ 𝔪) = ix-inr≀ κ 𝔪

-- Correctness lemmas of weakening, lifting, identity
ext≀≈𝕋₁pop : (κ : MSub Γ 𝔐 𝔑)(𝔪 : Π ⊩ τ ∈ 𝔐) → ix≀ (ext≀ Δ β κ) 𝔪 ≡ wk≀ (ix≀ κ 𝔪)
ext≀≈𝕋₁pop (x ◃ κ) ↓ = refl
ext≀≈𝕋₁pop (x ◃ κ) (↑ 𝔪) = ext≀≈𝕋₁pop κ 𝔪

lift≀≈𝕋₁pop : (κ : MSub Γ 𝔐 𝔑)(𝔪 : Γ ⊩ α ∈ 𝔐) → ix≀ (lift≀ Γ α κ) (↑ 𝔪) ≡ wk≀ (ix≀ κ 𝔪)
lift≀≈𝕋₁pop (x ◃ κ) ↓ = refl
lift≀≈𝕋₁pop (x ◃ κ) (↑ 𝔪) = lift≀≈𝕋₁pop κ 𝔪

id≀≈ms-unit : (Γ : Ctx)(𝔪 : Π ⊩ τ ∈ 𝔐) → ix≀ (id≀ Γ) 𝔪 ≡ ms-unit 𝔪
id≀≈ms-unit {𝔐 = Π ⊩ τ ≀ 𝔐} Γ ↓ = refl
id≀≈ms-unit {𝔐 = Π ⊩ τ ≀ 𝔐} Γ (↑_ {Δ}{β}{Γ = .Π}{.τ} 𝔪) = begin
      ix≀ (ext≀ Π τ (id≀ Γ)) 𝔪
  ≡⟨ ext≀≈𝕋₁pop (id≀ Γ) 𝔪 ⟩
      wk≀ (ix≀ (id≀ Γ) 𝔪)
  ≡⟨ cong (wk≀) (id≀≈ms-unit Γ 𝔪) ⟩
      wk≀ (ms-unit 𝔪)
  ≡⟨⟩
      wk≀ (𝕞𝕧𝕒𝕣 ∥ 𝔐 ∥ 𝔪 (𝕧𝕒𝕣 ∥ 𝔐 ∥ ∘ ∔.i₁))
  ≡⟨ 𝕋₁∘𝕞𝕧𝕒𝕣[𝕧𝕒𝕣] ↑_ 𝔪 (∔.i₁) ⟩
      𝕞𝕧𝕒𝕣 ∥ Π ⊩ τ ≀ 𝔐 ∥ (↑ 𝔪) (𝕧𝕒𝕣 ∥ Π ⊩ τ ≀ 𝔐 ∥ ∘ ∔.i₁)
  ∎ where open ≡-Reasoning

-- Inductive metasubstitution operations
-- Base
msub≀ : (𝔐 ▷ 𝕋) α Γ → MSub Γ 𝔐 𝔑 → (𝔑 ▷ 𝕋) α Γ
msub≀ t ζ = msub t (ix≀ ζ)
-- Parametrised
□msub≀ : (𝔐 ▷ 𝕋) α Γ → (Γ ↝ Δ) → MSub Δ 𝔐 𝔑 → (𝔑 ▷ 𝕋) α Δ
□msub≀ t ρ ζ = □msub t ρ (ix≀ ζ)
-- Linear
○msub≀ : (𝔐 ▷ 𝕋) α Γ → MSub Δ 𝔐 𝔑 → (𝔑 ▷ 𝕋) α (Γ ∔ Δ)
○msub≀ {Γ = Γ} t ζ = □msub≀ t (inl Γ) (inr≀ Γ ζ)

-- Syntactic sugar for metasubstitution application
_》 : (𝔑 ▷ 𝕋) α (Π ∔ Γ) → MSub Γ (Π ⊪ α) 𝔑
t 》  = t ◃ ◦
_《_ : (𝔐 ▷ 𝕋) α Γ → MSub Γ 𝔐 𝔑 → (𝔑 ▷ 𝕋) α Γ
_《_ = msub≀

infixr 25 _》
infix 15 _《_

-- Instantiation of a term in an extended context
inst : (Π ⊩ α ≀ 𝔐 ▷ 𝕋) β Γ → (𝔐 ▷ 𝕋) α (Π ∔ Γ) → (𝔐 ▷ 𝕋) β Γ
inst {Γ = Γ} h s = msub≀ h (s ◃ id≀ Γ)
