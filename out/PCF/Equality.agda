{-
This second-order equational theory was created from the following second-order syntax description:

syntax PCF

type
  N   : 0-ary
  _↣_ : 2-ary | r30
  B   : 0-ary

term
  app : α ↣ β  α  ->  β | _$_ l20
  lam : α.β  ->  α ↣ β | ƛ_ r10
  tr  : B
  fl  : B
  ze  : N
  su  : N  ->  N
  pr  : N  ->  N
  iz  : N  ->  B | 0?
  if  : B  α  α  ->  α
  fix : α.α  ->  α

theory
  (ƛβ) b : α.β  a : α |> app (lam(x.b[x]), a) = b[a]
  (ƛη) f : α ↣ β      |> lam (x. app(f, x))   = f
  (zz)       |> iz (ze)       = tr
  (zs) n : N |> iz (su (n)) = fl
  (ps) n : N |> pr (su (n)) = n
  (ift) t f : α |> if (tr, t, f) = t
  (iff) t f : α |> if (fl, t, f) = f
  (fix) t : α.α |> fix (x.t[x]) = t[fix (x.t[x])]
-}

module PCF.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import PCF.Signature
open import PCF.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution PCF:Syn
open import SOAS.Metatheory.SecondOrder.Equality PCF:Syn
open import SOAS.Metatheory

open PCF:Syntax
open import SOAS.Syntax.Shorthands PCFᵃ

private
  variable
    α β γ τ : PCFT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ PCF) α Γ → (𝔐 ▷ PCF) α Γ → Set where
  ƛβ  : ⁅ α ⊩ β ⁆ ⁅ α ⁆̣ ▹ ∅ ⊢ (ƛ 𝔞⟨ x₀ ⟩) $ 𝔟 ≋ₐ 𝔞⟨ 𝔟 ⟩
  ƛη  : ⁅ α ↣ β ⁆̣       ▹ ∅ ⊢      ƛ (𝔞 $ x₀) ≋ₐ 𝔞
  zz  : ⁅⁆              ▹ ∅ ⊢           0? ze ≋ₐ tr
  zs  : ⁅ N ⁆̣           ▹ ∅ ⊢       0? (su 𝔞) ≋ₐ fl
  ps  : ⁅ N ⁆̣           ▹ ∅ ⊢       pr (su 𝔞) ≋ₐ 𝔞
  ift : ⁅ α ⁆ ⁅ α ⁆̣     ▹ ∅ ⊢       if tr 𝔞 𝔟 ≋ₐ 𝔞
  iff : ⁅ α ⁆ ⁅ α ⁆̣     ▹ ∅ ⊢       if fl 𝔞 𝔟 ≋ₐ 𝔟
  fix : ⁅ α ⊩ α ⁆̣       ▹ ∅ ⊢   fix (𝔞⟨ x₀ ⟩) ≋ₐ 𝔞⟨ (fix (𝔞⟨ x₀ ⟩)) ⟩

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning
