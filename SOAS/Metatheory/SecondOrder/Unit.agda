
open import SOAS.Metatheory.Syntax

-- Unit law of metasubstitution
module SOAS.Metatheory.SecondOrder.Unit {T : Set}(Syn : Syntax {T}) where

open Syntax Syn

open import SOAS.Metatheory.FreeMonoid Syn

open import SOAS.Metatheory.SecondOrder.Metasubstitution Syn

open import SOAS.Families.Core {T}
open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Construction.Structure as Structure
open import SOAS.ContextMaps.Combinators
open import SOAS.ContextMaps.CategoryOfRenamings {T}
import SOAS.Abstract.Coalgebra {T} as →□
open →□.Sorted
open →□.Unsorted using (⊤ᵇ) renaming (Coalg to UCoalg ; Coalg⇒ to UCoalg⇒)
import SOAS.Abstract.Box {T} as □ ; open □.Sorted
open import SOAS.Abstract.Monoid
open import SOAS.Abstract.ExpStrength

open import SOAS.Coalgebraic.Monoid

open import SOAS.Metatheory Syn
open import SOAS.Metatheory.Monoid ⅀F ⅀:Str
open import SOAS.ContextMaps.Properties

open Theory

private
  variable
    Γ Δ Π : Ctx
    α β : T
    𝔛 𝔜 ℨ : Familyₛ

-- Metasubstitution unit is a coalgebra homomorphisem from ⊤
ms-unitᵇ⇒ : UCoalg⇒ ⊤ᵇ [ 𝔛 ⊸ (𝕋ᵇ 𝔛) ]ᵇ (λ _ → ms-unit)
ms-unitᵇ⇒ {𝔛} = record
  { ⟨r⟩ = λ{ {Γ = Γ}{Δ}{ρ} → iext (dext λ {Π} 𝔪 → sym (begin
        𝕣𝕖𝕟 𝔛 (ms-unit 𝔪) (Π ∔∣ ρ)
    ≡⟨ Renaming.𝕥⟨𝕞⟩ 𝔛 ⟩
        𝕞𝕧𝕒𝕣 𝔛 𝔪 (λ p → 𝕣𝕖𝕟 𝔛 (𝕧𝕒𝕣 𝔛 (inl Π p)) (Π ∔∣ ρ))
    ≡⟨ 𝕞≈₂ 𝔛 (λ v → Renaming.𝕥⟨𝕧⟩ 𝔛) ⟩
        𝕞𝕧𝕒𝕣 𝔛 𝔪 (λ v → 𝕧𝕒𝕣 𝔛 ((Π ∔∣ ρ) (inl Π v)))
    ≡⟨ 𝕞≈₂ 𝔛 (λ v → cong (𝕧𝕒𝕣 𝔛) (∔.+₁∘i₁ {f = id′ᵣ Π}{g = ρ})) ⟩
        𝕞𝕧𝕒𝕣 𝔛 𝔪 (λ v → 𝕧𝕒𝕣 𝔛 (∔.i₁ v))
    ∎))}
  } where open ≡-Reasoning

-- Right unit of metasubstitution
□msub-runitᵃ⇒ : MetaAlg⇒  𝔛 (𝕋ᵃ 𝔛) (□ᵃ 𝔛 (𝕋ᵃ 𝔛)) λ t ρ → □msub t ρ ms-unit
□msub-runitᵃ⇒ {𝔛} = record
  { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → dext λ ρ → begin
        □msub (𝕒𝕝𝕘 𝔛 t) ρ ms-unit
    ≡⟨ cong (λ - → - ms-unit) □MS.𝕥⟨𝕒⟩ ⟩
        𝕒𝕝𝕘 𝔛 (□estr [ 𝔛 ⊸ 𝕋ᵇ 𝔛 ]ᵇ (𝕋 𝔛) (⅀₁ □msub t) ρ ms-unit)
    ≡⟨ cong (𝕒𝕝𝕘 𝔛) (estr-unit′ ms-unitᵇ⇒) ⟩
        𝕒𝕝𝕘 𝔛 (⅀₁ (λ e′ → e′ ms-unit) (str ℐᴮ ⟅ 𝔛 ⇨ 𝕋 𝔛 ⟆ (⅀₁ □msub t) ρ))
    ≡˘⟨ cong (𝕒𝕝𝕘 𝔛) (str-nat₂ ((λ e′ → e′ ms-unit)) (⅀₁ □msub t) ρ) ⟩
        𝕒𝕝𝕘 𝔛 (str ℐᴮ (𝕋 𝔛) (⅀₁ (λ { h′ ς → h′ ς ms-unit }) (⅀₁ □msub t)) ρ)
    ≡˘⟨ congr ⅀.homomorphism (λ - → 𝕒𝕝𝕘 𝔛 (str ℐᴮ (𝕋 𝔛) - ρ)) ⟩
        𝕒𝕝𝕘 𝔛 (str ℐᴮ (𝕋 𝔛) (⅀₁ (λ{ t ρ → □msub t ρ ms-unit}) t) ρ)
    ∎ }
  ; ⟨𝑣𝑎𝑟⟩ = λ{ {v = v} → dext λ ρ → cong (λ - → - ms-unit) □MS.𝕥⟨𝕧⟩}
  ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{ε} → dext λ ρ → begin
        □msub (𝕞𝕧𝕒𝕣 𝔛 𝔪 ε) ρ ms-unit
    ≡⟨ cong (λ - → - ms-unit) □MS.𝕥⟨𝕞⟩ ⟩
        𝕤𝕦𝕓 𝔛 (ms-unit 𝔪) (copair (𝕋 𝔛) (λ v → □msub (ε v) ρ ms-unit) (𝕧𝕒𝕣 𝔛))
    ≡⟨ Substitution.𝕥⟨𝕞⟩ 𝔛 ⟩
        𝕞𝕧𝕒𝕣 𝔛 𝔪 (λ v → 𝕤𝕦𝕓 𝔛 (𝕧𝕒𝕣 𝔛 (∔.i₁ v)) (copair (𝕋 𝔛) (λ v → □msub (ε v) ρ ms-unit) (𝕧𝕒𝕣 𝔛)))
    ≡⟨ 𝕞≈₂ 𝔛 (λ v → begin
              𝕤𝕦𝕓 𝔛 (𝕧𝕒𝕣 𝔛 (∔.i₁ v)) (copair (𝕋 𝔛) (λ 𝔫 → □msub (ε 𝔫) ρ ms-unit) (𝕧𝕒𝕣 𝔛))
          ≡⟨ Mon.lunit (𝕋ᵐ 𝔛) ⟩
              copair (𝕋 𝔛) (λ 𝔫 → □msub (ε 𝔫) ρ ms-unit) (𝕧𝕒𝕣 𝔛) (∔.i₁ v)
          ≡⟨ copair∘i₁ (𝕋 𝔛) v ⟩
              □msub (ε v) ρ ms-unit
          ∎) ⟩
        𝕞𝕧𝕒𝕣 𝔛 𝔪 (λ v → □msub (ε v) ρ ms-unit)
    ∎ }
  } where open ≡-Reasoning

□msub-runit : (t : 𝕋 𝔛 α Γ)(ρ : Γ ↝ Δ)
           → □msub t ρ ms-unit ≡ 𝕣𝕖𝕟 𝔛 t ρ
□msub-runit {𝔛} t ρ = sym (cong (λ - → - ρ) (Renaming.𝕤𝕖𝕞! 𝔛 □msub-runitᵃ⇒ t))
