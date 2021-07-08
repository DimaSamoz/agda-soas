
-- Internal hom in families
module SOAS.Abstract.Hom {T : Set} where

open import SOAS.Common
open import SOAS.Construction.Structure
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core {T}
open import SOAS.Families.Isomorphism
open import SOAS.Families.BCCC

open import SOAS.Construction.Skew.SkewClosed

open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation.Dinatural using (dtHelper)


-- Heterogeneous action of a sorted family on a family
⟨_,_⟩ : Familyₛ → Family → Family
⟨ 𝒳 , Y ⟩ Γ = (Γ ~[ 𝒳 ]↝_) ⇾ Y

⟨-,-⟩F : Bifunctor 𝔽amₛ.op 𝔽amilies 𝔽amilies
⟨-,-⟩F = record
  { F₀ = λ{ (𝒳 , Y) → ⟨ 𝒳 , Y ⟩ }
  ; F₁ = λ{ (f , g) o {Δ} σ → g (o (f ∘ σ))  }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ{ {f = f , g} (p , p′) {Γ} {o} → dext′ (trans (cong (g ∘ o) (dext′ p)) p′) }
  }

-- Arrow mapping
⟨_,_⟩₁ : {𝒳 𝒳′ : Familyₛ} {Y Y′ : Family} → 𝒳′ ⇾̣ 𝒳 → Y ⇾ Y′ → (⟨ 𝒳 , Y ⟩ ⇾ ⟨ 𝒳′ , Y′ ⟩)
⟨ f , g ⟩₁ = Functor.₁ ⟨-,-⟩F (f , g)


-- Internal hom of sorted families
〖_,_〗 : Familyₛ → Familyₛ → Familyₛ
〖 X , Y 〗 τ = ⟨ X , Y τ ⟩

〖-,-〗F  : Bifunctor 𝔽amₛ.op 𝔽amiliesₛ 𝔽amiliesₛ
〖-,-〗F = record
  { F₀ = λ{ (X , Y) → 〖 X , Y 〗 }
  ; F₁ = λ{ (f , g) o {Δ} σ → g (o (f ∘ σ))  }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ{ {f = f , g} (p , p′) {x = h} → dext′ (trans (cong (g ∘ h) (dext′ p)) p′) }
  }

-- Arrow mapping
〖_,_〗₁ : {𝒳 𝒳′ 𝒴 𝒴′ : Familyₛ} → 𝒳′ ⇾̣ 𝒳 → 𝒴 ⇾̣ 𝒴′ → (〖 𝒳 , 𝒴 〗 ⇾̣ 〖 𝒳′ , 𝒴′ 〗)
〖 f , g 〗₁ h σ = g (h (f ∘ σ))

〖_,_〗ₗ : {𝒳 𝒳′ : Familyₛ} → 𝒳′ ⇾̣ 𝒳 → (𝒴 : Familyₛ) → (〖 𝒳 , 𝒴 〗 ⇾̣ 〖 𝒳′ , 𝒴 〗)
〖 f , Z 〗ₗ h σ = h (f ∘ σ)

〖_,_〗ᵣ : {𝒴 𝒴′ : Familyₛ} → (𝒳 : Familyₛ) → 𝒴 ⇾̣ 𝒴′ → (〖 𝒳 , 𝒴 〗 ⇾̣ 〖 𝒳 , 𝒴′ 〗)
〖 X , g 〗ᵣ h σ = g (h σ)


-- | Structure morphisms

i : (𝒳 : Familyₛ) → 〖 ℐ , 𝒳 〗 ⇾̣ 𝒳
i 𝒳 o = o id

i′ : (X : Family) → ⟨ ℐ , X ⟩ ⇾ X
i′ X o = o id

j : (𝒳 : Familyₛ) → ℐ ⇾̣ 〖 𝒳 , 𝒳 〗
j 𝒳 v σ = σ v

L : (𝒳 𝒴 𝒵 : Familyₛ) → 〖 𝒴 , 𝒵 〗 ⇾̣ 〖 〖 𝒳 , 𝒴 〗 , 〖 𝒳 , 𝒵 〗 〗
L 𝒳 Y Z o ς σ = o (λ v → ς v σ)

L′ : (𝒳 𝒴 : Familyₛ)(Z : Family) → ⟨ 𝒴 , Z ⟩ ⇾ ⟨ 〖 𝒳 , 𝒴 〗 , ⟨ 𝒳 , Z ⟩ ⟩
L′ 𝒳 𝒴 Z o ς σ = o (λ v → ς v σ)


-- Category of sorted families is skew-closed under the internal hom
𝔽amₛ:SkewClosed : SkewClosed 𝔽amiliesₛ
𝔽amₛ:SkewClosed = record
  { [-,-] = 〖-,-〗F
  ; unit = ℐ
  ; identity = ntHelper record { η = i  ; commute = λ f → refl }
  ; diagonal = dtHelper record { α = j ; commute = λ f → refl }
  ; L = L
  ; L-commute = refl
  ; Lj≈j = refl
  ; ijL≈id = refl
  ; iL≈i = refl
  ; ij≈id = refl
  ; pentagon = refl
  }


private
  variable
    𝒳 𝒴 𝒵 : Familyₛ
    Y Z : Family

-- ⟨X,-⟩ distributes over and factors out of products
⟨𝒳,Y×Z⟩≅⟨𝒳,Y⟩×⟨𝒳,Z⟩ : ⟨ 𝒳 , (Y ×ₘ Z) ⟩ ≅ₘ ⟨ 𝒳 , Y ⟩ ×ₘ ⟨ 𝒳 , Z ⟩
⟨𝒳,Y×Z⟩≅⟨𝒳,Y⟩×⟨𝒳,Z⟩  = record
  { from = λ h → (λ ρ → proj₁ (h ρ)) , λ ϱ → proj₂ (h ϱ)
  ; to = λ{ (bx , by) ρ → bx ρ , by ρ}
  ; iso = record { isoˡ = refl ; isoʳ = refl }
  }

-- ⟨X,-⟩ factors out of coproducts
⟨𝒳,Y⟩+⟨𝒳,Z⟩⇾⟨𝒳,Y+Z⟩ : ⟨ 𝒳 , Y ⟩ +ₘ ⟨ 𝒳 , Z ⟩ ⇾ ⟨ 𝒳 , (Y +ₘ Z) ⟩
⟨𝒳,Y⟩+⟨𝒳,Z⟩⇾⟨𝒳,Y+Z⟩ (inj₁ ox) σ = inj₁ (ox σ)
⟨𝒳,Y⟩+⟨𝒳,Z⟩⇾⟨𝒳,Y+Z⟩ (inj₂ oy) ς = inj₂ (oy ς)

-- Same properties for the hom
〖𝒳,𝒴×̣𝒵〗≅̣〖𝒳,𝒴〗×̣〖𝒳,𝒵〗 : 〖 𝒳 , 𝒴 ×̣ₘ 𝒵 〗 ≅̣ₘ 〖 𝒳 , 𝒴 〗 ×̣ₘ 〖 𝒳 , 𝒵 〗
〖𝒳,𝒴×̣𝒵〗≅̣〖𝒳,𝒴〗×̣〖𝒳,𝒵〗 = ≅ₘ→≅̣ₘ ⟨𝒳,Y×Z⟩≅⟨𝒳,Y⟩×⟨𝒳,Z⟩

〖𝒳,𝒴〗+̣〖𝒳,𝒵〗⇾̣〖𝒳,𝒴+̣𝒵〗 : 〖 𝒳 , 𝒴 〗 +̣ₘ 〖 𝒳 , 𝒵 〗 ⇾̣ 〖 𝒳 , (𝒴 +̣ₘ 𝒵) 〗
〖𝒳,𝒴〗+̣〖𝒳,𝒵〗⇾̣〖𝒳,𝒴+̣𝒵〗 = ⟨𝒳,Y⟩+⟨𝒳,Z⟩⇾⟨𝒳,Y+Z⟩
