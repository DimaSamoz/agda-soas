
open import SOAS.Metatheory.Syntax

-- Initial (⅀, 𝔛)-syntactic algebra 𝕋 𝔛 is the free ⅀-monoid on 𝔛
module SOAS.Metatheory.FreeMonoid {T : Set} (Syn : Syntax {T}) where

open Syntax Syn

open import SOAS.Common
open import SOAS.Families.Core {T}
open import SOAS.Context {T}
open import SOAS.Variable {T}
open import SOAS.Construction.Structure as Structure
open import SOAS.Abstract.Hom {T}
import SOAS.Abstract.Coalgebra {T} as →□ ; open →□.Sorted
import SOAS.Abstract.Box {T} as □ ; open □.Sorted

open import Categories.Monad

open import SOAS.Abstract.Monoid

open import SOAS.Coalgebraic.Map
open import SOAS.Coalgebraic.Monoid
open import SOAS.Coalgebraic.Strength
open import SOAS.Metatheory Syn


private
  variable
    α β : T
    Γ Δ Π : Ctx

module _ (𝔛 : Familyₛ) where
  open Theory 𝔛

  -- 𝕋 is a Σ-monoid
  Σ𝕋ᵐ : ΣMon 𝕋
  Σ𝕋ᵐ =   record
    { ᵐ = 𝕋ᵐ
    ; 𝑎𝑙𝑔 = 𝕒𝕝𝕘
    ; μ⟨𝑎𝑙𝑔⟩ = λ{ {σ = σ} t → begin
          𝕤𝕦𝕓 (𝕒𝕝𝕘 t) σ
      ≡⟨ Substitution.𝕥⟨𝕒⟩ ⟩
          𝕒𝕝𝕘 (str 𝕋ᴮ 𝕋 (⅀₁ 𝕤𝕦𝕓 t) σ)
      ≡⟨ cong 𝕒𝕝𝕘 (CoalgMon.str-eq 𝕋ᴹ 𝕋 ⅀:Str (⅀₁ 𝕤𝕦𝕓 t) σ) ⟩
          𝕒𝕝𝕘 (str (Mon.ᴮ 𝕋ᵐ) 𝕋 (⅀₁ 𝕤𝕦𝕓 t) σ)
      ∎ }
    } where open ≡-Reasoning

  -- Given a ⅀-monoid ℳ and interpretation ω : 𝔛 ⇾̣ ℳ,
  -- there is a unique homomorphic extension 𝕋 𝔛 ⇾̣ ℳ
  module FΣM {ℳ : Familyₛ}(Σℳᵐ : ΣMon ℳ) (ω : 𝔛 ⇾̣ ℳ) where
    open ΣMon Σℳᵐ renaming (𝑎𝑙𝑔 to ℳ𝑎𝑙𝑔 ; ᴮ to ℳᴮ ; ᵐ to ℳᵐ) public
    open Model ω renaming (ᵃ to ℳᵃ) public
    private module ℳ = ΣMon Σℳᵐ

    -- Metavariable operator of ℳ using ω and monoid multiplication, making
    -- ℳ into a syntactic algebra
    χ : 𝔛 ⇾̣ 〖 ℳ , ℳ 〗
    χ = μ ∘ ω


    open Semantics ℳᵃ public renaming (𝕤𝕖𝕞 to 𝕖𝕩𝕥)
    open SynAlg ℳᵃ
    open Coalgebraic μᶜ

    -- Extension is pointed coalgebra homomorphism
    𝕖𝕩𝕥ᵇ⇒ : Coalg⇒ 𝕋ᵇ ℳ.ᵇ 𝕖𝕩𝕥
    𝕖𝕩𝕥ᵇ⇒ = 𝕤𝕖𝕞ᵇ⇒ ℳ.ᵇ ℳᵃ record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → dext (λ ρ → begin
            μ (𝑎𝑙𝑔 t) (η ∘ ρ)
        ≡⟨ μ⟨𝑎𝑙𝑔⟩ t ⟩
            𝑎𝑙𝑔 (str ℳ.ᴮ ℳ (⅀₁ μ t) (η ∘ ρ))
        ≡⟨ cong 𝑎𝑙𝑔 (str-nat₁ (ηᴮ⇒ ℳᴮ) (⅀₁ ℳ.μ t) ρ) ⟩
            𝑎𝑙𝑔 (str ℐᴮ ℳ (⅀.F₁ (λ { h ς → h (λ v → η (ς v)) }) (⅀₁ ℳ.μ t)) ρ)
        ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str ℐᴮ ℳ - ρ)) ⟩
            𝑎𝑙𝑔 (str ℐᴮ ℳ (⅀.F₁ (λ{ t ρ → μ t (η ∘ ρ)}) t) ρ)
        ∎) }
      ; ⟨𝑣𝑎𝑟⟩ = dext′ ℳ.lunit
      ; ⟨𝑚𝑣𝑎𝑟⟩ = dext′ ℳ.assoc
      } where open ≡-Reasoning

    𝕖𝕩𝕥ᴮ⇒ : Coalgₚ⇒ 𝕋ᴮ ℳ.ᴮ 𝕖𝕩𝕥
    𝕖𝕩𝕥ᴮ⇒ = record { ᵇ⇒ = 𝕖𝕩𝕥ᵇ⇒ ; ⟨η⟩ = ⟨𝕧⟩ }

    -- Extension is monoid homomorphism
    μ∘𝕖𝕩𝕥 : MapEq₁ 𝕋ᴮ ℳ.𝑎𝑙𝑔 (λ t σ → 𝕖𝕩𝕥 (𝕤𝕦𝕓 t σ))
                           (λ t σ → μ (𝕖𝕩𝕥 t) (𝕖𝕩𝕥 ∘ σ))
    μ∘𝕖𝕩𝕥 = record
      { φ = 𝕖𝕩𝕥
      ; χ = χ
      ; f⟨𝑣⟩ = cong 𝕖𝕩𝕥 Substitution.𝕥⟨𝕧⟩
      ; f⟨𝑚⟩ = trans (cong 𝕖𝕩𝕥 Substitution.𝕥⟨𝕞⟩) ⟨𝕞⟩
      ; f⟨𝑎⟩ = λ{ {σ = σ}{t} → begin
            𝕖𝕩𝕥 (𝕤𝕦𝕓 (𝕒𝕝𝕘 t) σ)
        ≡⟨ cong 𝕖𝕩𝕥 Substitution.𝕥⟨𝕒⟩ ⟩
            𝕖𝕩𝕥 (𝕒𝕝𝕘 (str 𝕋ᴮ 𝕋 (⅀₁ 𝕤𝕦𝕓 t) σ))
        ≡⟨ ⟨𝕒⟩ ⟩
            𝑎𝑙𝑔 (⅀₁ 𝕖𝕩𝕥 (str 𝕋ᴮ 𝕋 (⅀₁ 𝕤𝕦𝕓 t) σ))
        ≡˘⟨ cong 𝑎𝑙𝑔 (str-nat₂ 𝕖𝕩𝕥 (⅀₁ 𝕤𝕦𝕓 t) σ) ⟩
            𝑎𝑙𝑔 (str 𝕋ᴮ ℳ (⅀.F₁ (λ { h ς → 𝕖𝕩𝕥 (h ς) }) (⅀₁ 𝕤𝕦𝕓 t)) σ)
        ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str 𝕋ᴮ ℳ - σ))  ⟩
            𝑎𝑙𝑔 (str 𝕋ᴮ ℳ (⅀₁ (λ{ t σ → 𝕖𝕩𝕥 (𝕤𝕦𝕓 t σ)}) t) σ)
        ∎ }
      ; g⟨𝑣⟩ = trans (μ≈₁ ⟨𝕧⟩) (Mon.lunit ℳ.ᵐ)
      ; g⟨𝑚⟩ = trans (μ≈₁ ⟨𝕞⟩) (Mon.assoc ℳ.ᵐ)
      ; g⟨𝑎⟩ = λ{ {σ = σ}{t} → begin
            μ (𝕖𝕩𝕥 (𝕒𝕝𝕘 t)) (𝕖𝕩𝕥 ∘ σ)
        ≡⟨ μ≈₁ ⟨𝕒⟩ ⟩
            μ (𝑎𝑙𝑔 (⅀₁ 𝕖𝕩𝕥 t)) (𝕖𝕩𝕥 ∘ σ)
        ≡⟨ μ⟨𝑎𝑙𝑔⟩ _ ⟩
            𝑎𝑙𝑔 (str ℳᴮ ℳ (⅀₁ μ (⅀₁ 𝕖𝕩𝕥 t)) (𝕖𝕩𝕥 ∘ σ))
        ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str ℳᴮ ℳ - (𝕖𝕩𝕥 ∘ σ))) ⟩
            𝑎𝑙𝑔 (str ℳᴮ ℳ (⅀₁ (μ ∘ 𝕖𝕩𝕥) t) (𝕖𝕩𝕥 ∘ σ))
        ≡⟨ cong 𝑎𝑙𝑔 (str-nat₁ 𝕖𝕩𝕥ᴮ⇒ ((⅀₁ (μ ∘ 𝕖𝕩𝕥) t)) σ) ⟩
            𝑎𝑙𝑔 (str 𝕋ᴮ ℳ (⅀.F₁ (λ { h′ ς → h′ (𝕖𝕩𝕥 ∘ ς) }) (⅀₁ (μ ∘ 𝕖𝕩𝕥) t)) σ)
        ≡˘⟨ congr ⅀.homomorphism (λ - → ℳ𝑎𝑙𝑔 (str 𝕋ᴮ ℳ - σ))  ⟩
            𝑎𝑙𝑔 (str 𝕋ᴮ ℳ (⅀₁ (λ{ t σ → μ (𝕖𝕩𝕥 t) (𝕖𝕩𝕥 ∘ σ)}) t) σ)
        ∎ }
      } where open ≡-Reasoning

    𝕖𝕩𝕥ᵐ⇒ : ΣMon⇒ Σ𝕋ᵐ Σℳᵐ 𝕖𝕩𝕥
    𝕖𝕩𝕥ᵐ⇒ = record { ᵐ⇒ = record
      { ⟨η⟩ = ⟨𝕧⟩
      ; ⟨μ⟩ = λ{ {t = t} → MapEq₁.≈ μ∘𝕖𝕩𝕥 t } }
      ; ⟨𝑎𝑙𝑔⟩ = ⟨𝕒⟩ }

    module 𝕖𝕩𝕥ᵐ⇒ = ΣMon⇒ 𝕖𝕩𝕥ᵐ⇒

    -- Interpretation map is equal to any homomorphism that factors through 𝔛 ⇾ ℳ
    module _ {g : 𝕋 ⇾̣ ℳ}
             (gᵐ⇒ : ΣMon⇒ Σ𝕋ᵐ Σℳᵐ g)
             (p : ∀{α Π}{𝔪 : 𝔛 α Π} → g (𝕞𝕧𝕒𝕣 𝔪 𝕧𝕒𝕣) ≡ ω 𝔪) where
      open ΣMon⇒ gᵐ⇒ renaming (⟨𝑎𝑙𝑔⟩ to g⟨𝑎𝑙𝑔⟩)

      gᵃ⇒ : SynAlg⇒ 𝕋ᵃ ℳᵃ g
      gᵃ⇒ = record
        { ⟨𝑎𝑙𝑔⟩ = g⟨𝑎𝑙𝑔⟩
        ; ⟨𝑣𝑎𝑟⟩ = ⟨η⟩
        ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{ε} → begin
            g (𝕞𝕧𝕒𝕣 𝔪 ε)                     ≡˘⟨ cong g (cong (𝕞𝕧𝕒𝕣 𝔪) (dext′ Substitution.𝕥⟨𝕧⟩)) ⟩
            g (𝕞𝕧𝕒𝕣 𝔪 (λ v → 𝕤𝕦𝕓 (𝕧𝕒𝕣 v) ε))  ≡˘⟨ cong g Substitution.𝕥⟨𝕞⟩ ⟩
            g (𝕤𝕦𝕓 (𝕞𝕧𝕒𝕣 𝔪 𝕧𝕒𝕣) ε)            ≡⟨ ⟨μ⟩ ⟩
            μ (g (𝕞𝕧𝕒𝕣 𝔪 𝕧𝕒𝕣)) (g ∘ ε)        ≡⟨ μ≈₁ p ⟩
            μ (ω 𝔪) (λ x → g (ε x))          ∎  }
        } where open ≡-Reasoning

      𝕖𝕩𝕥ᵐ! : {α : T}{Γ : Ctx}(t : 𝕋 α Γ) → 𝕖𝕩𝕥 t ≡ g t
      𝕖𝕩𝕥ᵐ! = 𝕤𝕖𝕞! gᵃ⇒


-- Free Σ-monoid functor
Famₛ→ΣMon :  Familyₛ → ΣMonoid
Famₛ→ΣMon 𝔛 = Theory.𝕋 𝔛 ⋉ (Σ𝕋ᵐ 𝔛)

open ΣMonoidStructure.Free

Free-ΣMon-Mapping : FreeΣMonoid.FreeMapping Famₛ→ΣMon
Free-ΣMon-Mapping = record
  { embed = λ {𝔛} 𝔪 → let open Theory 𝔛 in 𝕞𝕧𝕒𝕣 𝔪 𝕧𝕒𝕣
  ; univ = λ{ 𝔛 (ℳ ⋉ Σℳᵐ) ω → let open FΣM 𝔛 Σℳᵐ ω in record
    { extend = 𝕖𝕩𝕥 ⋉ 𝕖𝕩𝕥ᵐ⇒
    ; factor = trans ⟨𝕞⟩ (trans (μ≈₂ ⟨𝕧⟩) runit)
    ; unique = λ{ (g ⋉ gᵐ⇒) p {x = t} → sym (𝕖𝕩𝕥ᵐ! gᵐ⇒ p t) } }}
  }

Free:𝔽amₛ⟶Σ𝕄on : Functor 𝔽amiliesₛ Σ𝕄onoids
Free:𝔽amₛ⟶Σ𝕄on = FreeΣMonoid.FreeMapping.Free Free-ΣMon-Mapping

-- Σ-monoid monad on families
ΣMon:Monad : Monad 𝔽amiliesₛ
ΣMon:Monad = FreeΣMonoid.FreeMapping.FreeMonad Free-ΣMon-Mapping
