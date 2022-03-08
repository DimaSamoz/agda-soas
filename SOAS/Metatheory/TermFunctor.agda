
open import SOAS.Metatheory.Syntax

-- Initial (⅀, 𝔛)-syntactic algebra 𝕋 𝔛 is the free ⅀-monoid on 𝔛
module SOAS.Metatheory.TermFunctor {T : Set} (Syn : Syntax {T}) where

open Syntax Syn

open import SOAS.Common
open import SOAS.Families.Core {T}
open import SOAS.Context {T}
open import SOAS.Variable {T}
import SOAS.Abstract.Coalgebra {T} as →□ ; open →□.Sorted

open import Categories.Monad

open import SOAS.Coalgebraic.Map
open import SOAS.Metatheory Syn
open import SOAS.Metatheory.FreeMonoid Syn


private
  variable
    α β : T
    Γ Δ Π : Ctx

𝕋F : Functor 𝔽amiliesₛ 𝔽amiliesₛ
𝕋F = Monad.F ΣMon:Monad

module 𝕋F = Functor 𝕋F

open Theory
open Monad ΣMon:Monad

private
  variable
    𝔛 𝔜 : Familyₛ

-- Unit of monad
𝕦𝕟𝕚𝕥 : 𝔛 ⇾̣ 𝕋 𝔛
𝕦𝕟𝕚𝕥 {𝔛} 𝔪 = 𝕞𝕧𝕒𝕣 𝔛 𝔪 (𝕧𝕒𝕣 𝔛)

-- Functorial action of 𝕋
𝕋₁ : (𝔛 ⇾̣ 𝔜) → 𝕋 𝔛 ⇾̣ 𝕋 𝔜
𝕋₁ {𝔛}{𝔜} f t = FΣM.𝕖𝕩𝕥 𝔛 (Σ𝕋ᵐ 𝔜) (𝕦𝕟𝕚𝕥 ∘ f) t

-- Functorial action is a coalgebra homomorphism
𝕋₁ᵇ⇒ : (f : 𝔛 ⇾̣ 𝔜) → Coalg⇒ (𝕋ᵇ 𝔛) (𝕋ᵇ 𝔜) (𝕋₁ f)
𝕋₁ᵇ⇒ {𝔛}{𝔜} f = 𝕤𝕖𝕞ᵇ⇒ 𝔛 (𝕋ᵇ 𝔜) (record { 𝑎𝑙𝑔 = 𝕒𝕝𝕘 𝔜 ; 𝑣𝑎𝑟 = 𝕧𝕒𝕣 𝔜 ; 𝑚𝑣𝑎𝑟 = λ 𝔪 → 𝕤𝕦𝕓 𝔜 (𝕦𝕟𝕚𝕥 (f 𝔪)) }) (record
  { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → Renaming.⟨𝕒⟩ 𝔜 }
  ; ⟨𝑣𝑎𝑟⟩ = Renaming.⟨𝕧⟩ 𝔜
  ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{ε} → dext λ ρ → 𝕤𝕦𝕓ᶜ.r∘f 𝔜 } })

-- Naturality of syntactic constructors
𝕧𝕒𝕣-nat : (f : 𝔛 ⇾̣ 𝔜)(v : ℐ α Γ)
       → 𝕋₁ f (𝕧𝕒𝕣 𝔛 v) ≡ 𝕧𝕒𝕣 𝔜 v
𝕧𝕒𝕣-nat {𝔛 = 𝔛}{𝔜} f v = FΣM.⟨𝕧⟩ 𝔛 (Σ𝕋ᵐ 𝔜) (𝕦𝕟𝕚𝕥 ∘ f)

𝕒𝕝𝕘-nat : (f : 𝔛 ⇾̣ 𝔜)(t : ⅀ (𝕋 𝔛) α Γ)
       → 𝕋₁ f (𝕒𝕝𝕘 𝔛 t) ≡ 𝕒𝕝𝕘 𝔜 (⅀₁ (𝕋₁ f) t)
𝕒𝕝𝕘-nat {𝔛}{𝔜} f t = FΣM.⟨𝕒⟩ 𝔛 (Σ𝕋ᵐ 𝔜) (𝕦𝕟𝕚𝕥 ∘ f)

𝕞𝕧𝕒𝕣-nat : (f : 𝔛 ⇾̣ 𝔜)(𝔪 : 𝔛 α Γ)(ε : Γ ~[ 𝕋 𝔛 ]↝ Δ)
       → 𝕋₁ f (𝕞𝕧𝕒𝕣 𝔛 𝔪 ε) ≡ 𝕞𝕧𝕒𝕣 𝔜 (f 𝔪) (𝕋₁ f ∘ ε)
𝕞𝕧𝕒𝕣-nat {𝔛 = 𝔛}{𝔜} f 𝔪 ε = begin
      𝕋₁ f (𝕞𝕧𝕒𝕣 𝔛 𝔪 ε)
  ≡⟨⟩
      𝕖𝕩𝕥 (𝕞𝕧𝕒𝕣 𝔛 𝔪 ε)
  ≡⟨ ⟨𝕞⟩ ⟩
      𝕤𝕦𝕓 𝔜 (𝕞𝕧𝕒𝕣 𝔜 (f 𝔪) (𝕧𝕒𝕣 𝔜)) (𝕋₁ f ∘ ε)
  ≡⟨ Substitution.𝕥⟨𝕞⟩ 𝔜 ⟩
      𝕞𝕧𝕒𝕣 𝔜 (f 𝔪) (λ 𝔫 → 𝕤𝕦𝕓 𝔜 (𝕧𝕒𝕣 𝔜 𝔫) (𝕋₁ f ∘ ε))
  ≡⟨ cong (𝕞𝕧𝕒𝕣 𝔜 (f 𝔪)) (dext (λ 𝔫 → lunit 𝔜)) ⟩
      𝕞𝕧𝕒𝕣 𝔜 (f 𝔪) (𝕋₁ f ∘ ε)
  ∎
  where
  open ≡-Reasoning
  open FΣM 𝔛 (Σ𝕋ᵐ 𝔜) (𝕦𝕟𝕚𝕥 ∘ f) using (𝕖𝕩𝕥 ; ⟨𝕞⟩)
