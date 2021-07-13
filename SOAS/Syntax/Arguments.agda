
-- Interpretation of signature arities
module SOAS.Syntax.Arguments {T : Set} where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Variable
open import SOAS.Families.Core {T}

open import Data.List.Base using ([] ; _∷_ ; List)
open import Data.Product
open import Data.Unit

-- List of arities as a product of terms in extended contexts
Arg : List (Ctx × T) → Familyₛ → Family
Arg []             𝒳 Γ = ⊤
Arg ((Θ , τ) ∷ []) 𝒳 Γ = 𝒳 τ (Θ ∔ Γ)
Arg ((Θ , τ) ∷ as) 𝒳 Γ = 𝒳 τ (Θ ∔ Γ) × Arg as 𝒳 Γ

-- Functorial action and laws
Arg₁ : {𝒳 𝒴 : Familyₛ} (as : List (Ctx × T))
     → (𝒳 ⇾̣ 𝒴) → Arg as 𝒳 ⇾ Arg as 𝒴
Arg₁ [] f tt = tt
Arg₁ ((Θ , τ) ∷ []) f t = f t
Arg₁ ((Θ , τ) ∷ (Θ′ , τ′) ∷ as) f (t , ts) = (f t) , (Arg₁ ((Θ′ , τ′) ∷ as) f ts)

Arg-id : {𝒳 : Familyₛ}{Γ : Ctx}(as : List (Ctx × T))(ts : Arg as 𝒳 Γ)
       → Arg₁ as id ts ≡ ts
Arg-id [] ts = refl
Arg-id (x ∷ []) t = refl
Arg-id (x ∷ y ∷ ys) (t , ts) = cong (_ ,_) (Arg-id (y ∷ ys) ts)

Arg-∘ : {𝒳 𝒴 𝒵 : Familyₛ}{Γ : Ctx}(as : List (Ctx × T))
      → {f : 𝒳 ⇾̣ 𝒴}{g : 𝒴 ⇾̣ 𝒵}
      → (ts : Arg as 𝒳 Γ)
      → Arg₁ as (g ∘ f) ts
      ≡ Arg₁ as g (Arg₁ as f ts)
Arg-∘ [] ts = refl
Arg-∘ (x ∷ []) t = refl
Arg-∘ (x ∷ y ∷ ys) (t , ts) = cong (_ ,_) (Arg-∘ (y ∷ ys) ts)

Arg-resp : {𝒳 𝒴 : Familyₛ}{Γ : Ctx}(as : List (Ctx × T))
         → {f g : 𝒳 ⇾̣ 𝒴}
         → ({τ : T}{Δ : Ctx}(x : 𝒳 τ Δ) → f x ≡ g x)
         → (ts : Arg as 𝒳 Γ)
         → Arg₁ as f ts ≡ Arg₁ as g ts
Arg-resp [] p ts = refl
Arg-resp (x ∷ []) p t = p t
Arg-resp (x ∷ y ∷ ys) p (t , ts) = cong₂ _,_ (p t) (Arg-resp (y ∷ ys) p ts)

ArgF : List (Ctx × T) → Functor 𝔽amiliesₛ 𝔽amilies
ArgF as = record
  { F₀ = Arg as
  ; F₁ = Arg₁ as
  ; identity = Arg-id as _
  ; homomorphism = Arg-∘ as _
  ; F-resp-≈ = λ p → Arg-resp as (λ _ → p) _
  }
