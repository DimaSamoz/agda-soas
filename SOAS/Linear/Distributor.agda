
-- Linear distributor map
module SOAS.Linear.Distributor {T : Set} where

open import SOAS.Families.Core {T}
open import SOAS.Families.Discrete {T}
open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.ContextMaps.Combinators
open import SOAS.ContextMaps.Properties
open import SOAS.ContextMaps.CategoryOfRenamings

open import SOAS.Linear.Tensor
open import SOAS.Linear.Exponential

import SOAS.Abstract.Coalgebra as →□ ; open →□.Sorted
import SOAS.Abstract.Box as □ ; open □.Sorted
open import SOAS.Abstract.Hom


private
  variable
    X Y : Family
    𝒳 𝒴 𝒵 𝒲 𝒫 𝒬  : Familyₛ
    Γ Δ Θ Ξ : Ctx
    α τ : T

-- Distribution of linear exponentials over homs
dist : (X : Family) → (ℐ ⇾̣ 𝒴) → (𝒵 : Familyₛ)
     → (X ⊸ 〖 𝒴 , 𝒵 〗) ⇾̣ 〖 X ⊸ 𝒴 , X ⊸ 𝒵 〗
dist {𝒴} X η 𝒵 {τ}{Γ} l {Δ} σ {Θ} x =
  l x (copair 𝒴 (λ v → σ v x) (η ∘ inr Δ))

-- Naturality
dist-nat₁ : {X Y : Family}{𝒵 𝒲 : Familyₛ}
            (f : Y ⇾ X)(η : ℐ ⇾̣ 𝒵)
            (l : (X ⊸ 〖 𝒵 , 𝒲 〗) α Γ)(σ : Γ ~[ X ⊸ 𝒵 ]↝ Δ)(y : Y Θ)
          → dist X η 𝒲 l σ (f y)
          ≡ dist Y η 𝒲 (l ∘ f) (λ v → σ v ∘ f) y
dist-nat₁ f η l σ y = refl

dist-nat₂ : (X : Family){𝒵 : Familyₛ}
            (η𝒴 : ℐ ⇾̣ 𝒴)(η𝒵 : ℐ ⇾̣ 𝒵)(𝒲 : Familyₛ)
            (f : 𝒴 ⇾̣ 𝒵)(fη≡η𝒵 : ∀{α Γ} → (v : ℐ α Γ) → f (η𝒴 v) ≡ η𝒵 v)
            (l : (X ⊸ 〖 𝒵 , 𝒲 〗) α Γ)(σ : Γ ~[ X ⊸ 𝒴 ]↝ Δ)(x : X Θ)
          → dist X η𝒵 𝒲 l (λ v → f ∘ σ v) x
          ≡ dist X η𝒴 𝒲 (λ x ς → l x (f ∘ ς)) σ x
dist-nat₂ {𝒴}{Δ = Δ} X {𝒵} η𝒴 η𝒵 𝒲 f fη≡η𝒵 l σ x =  cong (l x) (dext λ v → begin
      copair 𝒵 (λ v → f (σ v x)) (η𝒵 ∘ inr Δ) v
  ≡˘⟨ copair≈₂ 𝒵 (λ v → f (σ v x)) (λ v → fη≡η𝒵 (inr Δ v)) ⟩
      copair 𝒵 (λ v → f (σ v x)) (f ∘ η𝒴 ∘ inr Δ) v
  ≡˘⟨ f∘copair 𝒴 f (λ v → σ v x) (η𝒴 ∘ inr Δ) v ⟩
      f (copair 𝒴 (λ v → σ v x) (η𝒴 ∘ inr Δ) v)
  ∎) where open ≡-Reasoning

dist-nat₃ : (X : Family){𝒴 𝒵 𝒲 : Familyₛ}
            (η : ℐ ⇾̣ 𝒴)(f : 𝒵 ⇾̣ 𝒲)
            (l : (X ⊸ 〖 𝒴 , 𝒵 〗) α Γ)(σ : Γ ~[ X ⊸ 𝒴 ]↝ Δ)(x : X Θ)
          → f (dist X η 𝒵 l σ x)
          ≡ dist X η 𝒲 (λ x → f ∘ l x) σ x
dist-nat₃ X η f l σ x = refl

-- | Compatibility with closed structure

--                 dist                   〖κ°,id〗               i
--  X ⊸ 〖 ℐ , 𝒴 〗─────〖 X ⊸ ℐ , X ⊸ 𝒴 〗───────〖 ℐ , X ⊸ 𝒴 〗───── X ⊸ 𝒴
--       ╰──────────────────────────────────────────────────────────────╯
--                                X ⊸ i
--
dist-i : (𝒴 : Familyₛ)(l : (X ⊸ (□ 𝒴)) α Γ)(x : X Δ)
           → dist X id 𝒴 l (κ° X) x ≡ l x id
dist-i {X}{Γ = Γ}{Δ} 𝒴 l x = cong (l x) (dext′ (∔.+-η {A = Γ}{Δ}))

--     κ°         X ⊸ j                  dist
--  ℐ ──── X ⊸ ℐ ─────── X ⊸ 〖 𝒴 , 𝒴 〗──────〖 X ⊸ 𝒴, X ⊸ 𝒴 〗
--  ╰──────────────────────────────────────────────────╯
--                            j
--
dist-j : {𝒴 : Familyₛ}(η : ℐ ⇾̣ 𝒴)(v : ℐ α Γ)(σ : Γ ~[ X ⊸ 𝒴 ]↝ Δ)(x : X Θ)
        → dist X η 𝒴 (j 𝒴 ∘ κ° X v) σ x ≡ σ v x
dist-j {𝒴 = 𝒴} η v σ x = copair∘inl 𝒴 v

--                  X ⊸ L                        dist                           〖id, dist〗
--  X ⊸〖 𝒴 , 𝒵 〗 ────── X ⊸〖〖𝒲,𝒴〗,〖𝒲,𝒵〗〗─────〖 X ⊸〖𝒲,𝒴〗, X ⊸〖𝒲,𝒵〗〗──────────〖 X ⊸〖𝒲,𝒴〗,〖 X ⊸ 𝒲, X ⊸ 𝒵 〗〗
--       ╰───────〖 X ⊸ 𝒴 , X ⊸ 𝒵 〗───────〖〖 X ⊸ 𝒲 , X ⊸ 𝒴 〗,〖 X ⊸ 𝒲 , X ⊸ 𝒵 〗〗──────────────╯
--         dist                        L                                                〖dist, id〗
--
dist-L : (l : (X ⊸ 〖 𝒴 , 𝒵 〗) α Γ) (η : ℐ ⇾̣ 𝒲) (f : 𝒲 ⇾̣ 𝒴)
          (σ : Γ ~[ (X ⊸ 〖 𝒲 , 𝒴 〗) ]↝ Δ) (ς : Δ ~[ X ⊸ 𝒲 ]↝ Θ)(x : X Ξ)
        → dist X η 𝒵 (dist {𝒴 = 〖 𝒲 , 𝒴 〗} X (λ v σ → f (σ v)) 〖 𝒲 , 𝒵 〗 (L 𝒲 𝒴 𝒵 ∘ l) σ) ς x
        ≡ L (X ⊸ 𝒲) (X ⊸ 𝒴) (X ⊸ 𝒵) (dist X (f ∘ η) 𝒵 l) (λ v → dist X η 𝒴 (σ v)) ς x
dist-L {X} {𝒴} {𝒵} {Γ = Γ} {𝒲} {Δ} {Θ} l η f σ ς x = cong (l x) (dext (lemma σ x))
  where
  open ≡-Reasoning
  lemma : {Γ : Ctx}(σ : Γ ~[ X ⊸ 〖 𝒲 , 𝒴 〗 ]↝ Δ)(x : X Ξ) (v : ℐ τ (Γ ∔ Ξ))
        → copair 〖 𝒲 , 𝒴 〗 (λ v → σ v x) (λ v σ → f (σ (inr Δ v))) v
            (copair 𝒲 (λ v → ς v x) (η ∘ inr Θ))
        ≡ copair 𝒴 (λ v → dist X η 𝒴 (σ v) ς x) (f ∘ η ∘ inr Θ) v
  lemma {Γ = ∅} σ x v = cong f (copair∘inr 𝒲 {σ = λ v → ς v x} v)
  lemma {Γ = α ∙ Γ} σ x new = refl
  lemma {Γ = α ∙ Γ} σ x (old v) = lemma (σ ∘ old) x v

-- Interaction of distributor and currying
--                        dist                                      〖id, curry°〗
--  X ⊗ Y ⊸〖𝒵,𝒲〗───────────────────〖 X ⊗ Y ⊸ 𝒵, X ⊗ Y ⊸ 𝒲 〗────────────────────────────────〖 X ⊗ Y ⊸ 𝒵, X ⊸ Y ⊸ 𝒲 〗
--      ╰─────── X ⊸ Y ⊸ 〖𝒵,𝒲〗───────── X ⊸〖 Y ⊸ 𝒵, Y ⊸ 𝒲 〗──────〖 X ⊸ Y ⊸ 𝒵, X ⊸ Y ⊸ 𝒲 〗────────────╯
--        curry                  X ⊸ dist                        dist                           〖curry°, id〗
--
dist-curry° : (η : ℐ ⇾̣ 𝒵)(l : (X ⊗ Y ⊸ 〖 𝒵 , 𝒲 〗) α Γ)(σ : Γ ~[ (X ⊗ Y) ⊸ 𝒵 ]↝ Δ)(x : X Θ)(y : Y Ξ)
            → curry° 𝒲 (dist (X ⊗ Y) η 𝒲 l σ) x y
            ≡ dist {𝒴 = Y ⊸ 𝒵} X (λ v → η ∘ κ° Y v) (Y ⊸ 𝒲) ((dist Y η 𝒲 ∘ curry° (〖 𝒵 , 𝒲 〗) l)) (curry° 𝒵 ∘ σ) x y
dist-curry° {𝒵} {X} {Y} {𝒲 = 𝒲} {Γ = Γ} {Δ} {Θ} {Ξ} η l σ x y = begin
      curry° 𝒲 (dist (X ⊗ Y) η 𝒲 l σ) x y
  ≡⟨⟩
      assocˡ 𝒲 Δ Θ Ξ (l (x ⊹ y) (copair 𝒵 (λ v → σ v (x ⊹ y)) (η ∘ inr Δ)))
  ≡⟨ assocˡ-hom₁ 𝒵 𝒲 Δ (l (x ⊹ y)) ⟩
      l (x ⊹ y) (λ v → assocˡ 𝒵 Δ Θ Ξ (copair 𝒵 (λ v → σ v (x ⊹ y)) (η ∘ inr Δ) v))
  ≡⟨ cong (l (x ⊹ y)) (dext λ v → begin
        assocˡ 𝒵 Δ Θ Ξ (copair 𝒵 (λ v → σ v (x ⊹ y)) (η ∘ inr Δ) v)
    ≡⟨ f∘copair 𝒵 (assocˡ 𝒵 Δ Θ Ξ) (λ v → σ v (x ⊹ y)) (η ∘ inr Δ) v ⟩
        copair 𝒵 (λ v → curry° 𝒵 (σ v) x y) (assocˡ 𝒵 Δ Θ Ξ ∘ η ∘ inr Δ) v
    ≡⟨ copair≈₂ 𝒵 (λ v → curry° 𝒵 (σ v) x y) (λ v → begin
          assocˡ 𝒵 Δ Θ Ξ  (η  (inr Δ v))
      ≡˘⟨ assocˡ-nat Δ η (inr Δ v) ⟩
          η (assocˡ ℐ Δ Θ Ξ (inr Δ v))
      ≡⟨ cong η (assocˡ≈↝assocˡ Δ (inr Δ v)) ⟩
          η (↝assocˡ Δ Θ Ξ (inr Δ v))
      ≡⟨ cong η (copair∘inr ℐ {σ = inl (Δ ∔ Θ) ∘ inl Δ} v) ⟩
          η (copair ℐ (λ v → inl (Δ ∔ Θ) (inr Δ v)) (inr (Δ ∔ Θ)) v)
      ≡⟨ f∘copair ℐ η (λ v → κ° Y (inr Δ v) y) (inr (Δ ∔ Θ)) v ⟩
          copair 𝒵 (λ v → η (κ° Y (inr Δ v) y)) (η ∘ inr (Δ ∔ Θ)) v
      ∎) ⟩
        copair 𝒵 (λ v → curry° 𝒵 (σ v) x y) (copair 𝒵 (λ v → η (κ° Y (inr Δ v) y)) (η ∘ inr (Δ ∔ Θ))) v
    ≡˘⟨ copair∘assocˡ 𝒵 (λ v → curry° 𝒵 (σ v) x y) (λ v → η (κ° Y (inr Δ v) y)) (η ∘ inr (Δ ∔ Θ)) v ⟩
        copair 𝒵 (copair 𝒵 (λ v → curry° 𝒵 (σ v) x y) (λ v → η (κ° Y (inr Δ v) y))) (η ∘ inr (Δ ∔ Θ)) (assocˡ ℐ Γ Θ Ξ v)
    ≡˘⟨ copair≈₁ 𝒵 (η ∘ inr (Δ ∔ Θ)) {assocˡ ℐ Γ Θ Ξ v} (copair° Γ) ⟩
        copair 𝒵 (λ v → copair (Y ⊸ 𝒵) (λ v {Ξ} y → curry° 𝒵 (σ v) x y) (λ v y → η (κ° Y (inr Δ v) y)) v y) (η ∘ inr (Δ ∔ Θ)) (assocˡ ℐ Γ Θ Ξ v)
    ∎) ⟩
      l (x ⊹ y) (λ v → copair 𝒵 (λ v → copair (Y ⊸ 𝒵) (λ v {Ξ} y → curry° 𝒵 (σ v) x y) (λ v y → η (κ° Y (inr Δ v) y)) v y) (η ∘ inr (Δ ∔ Θ)) (assocˡ ℐ Γ Θ Ξ v))
  ≡˘⟨ assocˡ-hom₂ 𝒲 Γ ((l (x ⊹ y))) (copair 𝒵 (λ v → copair (Y ⊸ 𝒵) (λ v {Ξ} y → curry° 𝒵 (σ v) x y) (λ v y → η (κ° Y (inr Δ v) y)) v y) (η ∘ inr (Δ ∔ Θ))) ⟩
      assocˡ 〖 𝒵 , 𝒲 〗 Γ Θ Ξ (l (x ⊹ y)) (copair 𝒵 (λ v → copair (Y ⊸ 𝒵) (λ v {Ξ} y → curry° 𝒵 (σ v) x y) (λ v y → η (κ° Y (inr Δ v) y)) v y) (η ∘ inr (Δ ∔ Θ)))
  ≡⟨⟩
      dist {𝒴 = Y ⊸ 𝒵} X (λ v → η ∘ κ° Y v) (Y ⊸ 𝒲) (dist Y η 𝒲 ∘ curry° (〖 𝒵 , 𝒲 〗) l) (curry° 𝒵 ∘ σ) x y
  ∎ where open ≡-Reasoning

-- | Coalgebra structure on linear exponentials

-- Extending a box over a linear exponential
⊸□ : (𝒴 : Familyₛ) → (X ⊸ □ 𝒴) ⇾̣ □ (X ⊸ 𝒴)
⊸□ {X} 𝒴 l ρ {Θ} x = dist X id 𝒴 l (κ° X ∘ ρ) x

-- Pointed coalgebras can be linearly parametrised by a family
_⊸ᵇ_ : (X : Family) → Coalg 𝒴 → Coalg (X ⊸ 𝒴)
_⊸ᵇ_ {𝒴} X 𝒴ᵇ = record
  { r = λ l ρ {Δ} x → ⊸□ 𝒴 r ρ (l x)
  ; counit = λ{ {Γ = Γ}{t} → dext (λ {Δ} x → trans (r≈₂ (Concatʳ.identity Δ {Γ})) counit) }
  ; comult = λ{ {Γ = Γ}{Δ}{Θ}{ρ = ρ}{ϱ}{l} → dext (λ {Ξ} x → trans (r≈₂ (Functor.homomorphism (–∔F Ξ) {Γ}{Δ})) comult) }
  } where open Coalg 𝒴ᵇ

_⊸ᴮ_ : (X : Family) → Coalgₚ 𝒴 → Coalgₚ (X ⊸ 𝒴)
_⊸ᴮ_ {𝒴} X 𝒴ᴮ = record
  { ᵇ = X ⊸ᵇ ᵇ
  ; η = λ{ {Γ = Γ} v _ → η (inl Γ v)}
  ; r∘η = λ{ {Γ = Γ}{Δ}{v}{ρ} → dext (λ {Θ} x → begin
        r (η (inl Γ v)) (copair ℐ (inl Δ ∘ ρ) (inr Δ))
    ≡˘⟨ r≈₂ (λ{ {x = v} → ∔.[]∘+₁ {f = ρ} }) ⟩
        r (η (inl Γ v)) (copair ℐ (inl Δ)(inr Δ) ∘ (ρ ∣∔ Θ))
    ≡⟨ r≈₂ (λ{ {x = v} → ∔.+-η {A = Δ}{Θ} }) ⟩
        r (η (inl Γ v)) (ρ ∣∔ Θ)
    ≡⟨ r∘η ⟩
        η ((ρ ∣∔ Θ) (inl Γ v))
    ≡⟨ cong η (copair∘inl ℐ v) ⟩
        η (inl Δ (ρ v))
    ∎) }
  }
  where
  open Coalgₚ 𝒴ᴮ
  open ≡-Reasoning

κ°ᵇ⇒ : (X : Family) → Coalg⇒ ℐᵇ (X ⊸ᵇ ℐᵇ) (κ° X)
κ°ᵇ⇒ X = record { ⟨r⟩ = λ{ {ρ = ρ}{t} → dext λ x → sym (∔.inject₁ {f = inl _ ∘ ρ}{g = inr _}) } }

κ°ᴮ⇒ : (X : Family) → Coalgₚ⇒ ℐᴮ (X ⊸ᴮ ℐᴮ) (κ° X)
κ°ᴮ⇒ X = record { ᵇ⇒ = κ°ᵇ⇒ X ; ⟨η⟩ = refl }
