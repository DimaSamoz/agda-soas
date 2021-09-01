{-
This second-order equational theory was created from the following second-order syntax description:

syntax FOL

type
  * : 0-ary
  N : 0-ary

term
  false : * | ⊥
  or    : *  *  ->  * | _∨_ l20
  true  : * | ⊤
  and   : *  *  ->  * | _∧_ l20
  not   : *  ->  * | ¬_ r50
  eq    : N  N  ->  * | _≟_ l20
  all   : N.*  ->  * | ∀′
  ex    : N.*  ->  * | ∃′

theory
  (⊥U∨ᴸ) a |> or (false, a) = a
  (⊥U∨ᴿ) a |> or (a, false) = a
  (∨A) a b c |> or (or(a, b), c) = or (a, or(b, c))
  (∨C) a b |> or(a, b) = or(b, a)
  (⊤U∧ᴸ) a |> and (true, a) = a
  (⊤U∧ᴿ) a |> and (a, true) = a
  (∧A) a b c |> and (and(a, b), c) = and (a, and(b, c))
  (∧D∨ᴸ) a b c |> and (a, or (b, c)) = or (and(a, b), and(a, c))
  (∧D∨ᴿ) a b c |> and (or (a, b), c) = or (and(a, c), and(b, c))
  (⊥X∧ᴸ) a |> and (false, a) = false
  (⊥X∧ᴿ) a |> and (a, false) = false
  (¬N∨ᴸ) a |> or (not (a), a) = false
  (¬N∨ᴿ) a |> or (a, not (a)) = false
  (∧C) a b |> and(a, b) = and(b, a)
  (∨I) a |> or(a, a) = a
  (∧I) a |> and(a, a) = a
  (¬²) a |> not(not (a)) = a
  (∨D∧ᴸ) a b c |> or (a, and (b, c)) = and (or(a, b), or(a, c))
  (∨D∧ᴿ) a b c |> or (and (a, b), c) = and (or(a, c), or(b, c))
  (⊤X∨ᴸ) a |> or (true, a) = true
  (⊤X∨ᴿ) a |> or (a, true) = true
  (¬N∧ᴸ) a |> and (not (a), a) = false
  (¬N∧ᴿ) a |> and (a, not (a)) = false
  (DM∧) a b |> not (and (a, b)) = or (not(a), not(b))
  (DM∨) a b |> not (or (a, b)) = and (not(a), not(b))
  (DM∀) p : N.* |> not (all (x. p[x])) = ex  (x. not(p[x]))
  (DM∃) p : N.* |> not (ex  (x. p[x])) = all (x. not(p[x]))
  (∀D∧) p q : N.* |> all (x. and(p[x], q[x])) = and (all(x.p[x]), all(x.q[x]))
  (∃D∨) p q : N.* |> ex (x. or(p[x], q[x])) = or (ex(x.p[x]), ex(x.q[x]))
  (∧P∀ᴸ) p : *  q : N.* |> and (p, all(x.q[x])) = all (x. and(p, q[x]))
  (∧P∃ᴸ) p : *  q : N.* |> and (p, ex (x.q[x])) = ex  (x. and(p, q[x]))
  (∨P∀ᴸ) p : *  q : N.* |> or  (p, all(x.q[x])) = all (x. or (p, q[x]))
  (∨P∃ᴸ) p : *  q : N.* |> or  (p, ex (x.q[x])) = ex  (x. or (p, q[x]))
  (∧P∀ᴿ) p : N.*  q : * |> and (all(x.p[x]), q) = all (x. and(p[x], q))
  (∧P∃ᴿ) p : N.*  q : * |> and (ex (x.p[x]), q) = ex  (x. and(p[x], q))
  (∨P∀ᴿ) p : N.*  q : * |> or  (all(x.p[x]), q) = all (x. or (p[x], q))
  (∨P∃ᴿ) p : N.*  q : * |> or  (ex (x.p[x]), q) = ex  (x. or (p[x], q))
  (∀Eᴸ) p : N.*  n : N |> all (x.p[x]) = and (p[n], all(x.p[x]))
  (∃Eᴸ) p : N.*  n : N |> ex  (x.p[x]) = or  (p[n], ex (x.p[x]))
  (∀Eᴿ) p : N.*  n : N |> all (x.p[x]) = and (all(x.p[x]), p[n])
  (∃Eᴿ) p : N.*  n : N |> ex  (x.p[x]) = or  (ex (x.p[x]), p[n])
  (∃⟹) p : N.*  q : * |> imp (ex (x.p[x]), q) = all (x. imp(p[x], q))
  (∀⟹) p : N.*  q : * |> imp (all(x.p[x]), q) = ex  (x. imp(p[x], q))
-}

module FOL.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import FOL.Signature
open import FOL.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution FOL:Syn
open import SOAS.Metatheory.SecondOrder.Equality FOL:Syn

private
  variable
    α β γ τ : FOLT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ FOL) α Γ → (𝔐 ▷ FOL) α Γ → Set where
  ⊥U∨ᴸ : ⁅ * ⁆̣               ▹ ∅ ⊢                  ⊥ ∨ 𝔞 ≋ₐ 𝔞
  ∨A   : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣   ▹ ∅ ⊢            (𝔞 ∨ 𝔟) ∨ 𝔠 ≋ₐ 𝔞 ∨ (𝔟 ∨ 𝔠)
  ∨C   : ⁅ * ⁆ ⁅ * ⁆̣         ▹ ∅ ⊢                  𝔞 ∨ 𝔟 ≋ₐ 𝔟 ∨ 𝔞
  ⊤U∧ᴸ : ⁅ * ⁆̣               ▹ ∅ ⊢                  ⊤ ∧ 𝔞 ≋ₐ 𝔞
  ∧A   : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣   ▹ ∅ ⊢            (𝔞 ∧ 𝔟) ∧ 𝔠 ≋ₐ 𝔞 ∧ (𝔟 ∧ 𝔠)
  ∧D∨ᴸ : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣   ▹ ∅ ⊢            𝔞 ∧ (𝔟 ∨ 𝔠) ≋ₐ (𝔞 ∧ 𝔟) ∨ (𝔞 ∧ 𝔠)
  ⊥X∧ᴸ : ⁅ * ⁆̣               ▹ ∅ ⊢                  ⊥ ∧ 𝔞 ≋ₐ ⊥
  ¬N∨ᴸ : ⁅ * ⁆̣               ▹ ∅ ⊢              (¬ 𝔞) ∨ 𝔞 ≋ₐ ⊥
  ∧C   : ⁅ * ⁆ ⁅ * ⁆̣         ▹ ∅ ⊢                  𝔞 ∧ 𝔟 ≋ₐ 𝔟 ∧ 𝔞
  ∨I   : ⁅ * ⁆̣               ▹ ∅ ⊢                  𝔞 ∨ 𝔞 ≋ₐ 𝔞
  ∧I   : ⁅ * ⁆̣               ▹ ∅ ⊢                  𝔞 ∧ 𝔞 ≋ₐ 𝔞
  ¬²   : ⁅ * ⁆̣               ▹ ∅ ⊢                ¬ (¬ 𝔞) ≋ₐ 𝔞
  ∨D∧ᴸ : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣   ▹ ∅ ⊢            𝔞 ∨ (𝔟 ∧ 𝔠) ≋ₐ (𝔞 ∨ 𝔟) ∧ (𝔞 ∨ 𝔠)
  ⊤X∨ᴸ : ⁅ * ⁆̣               ▹ ∅ ⊢                  ⊤ ∨ 𝔞 ≋ₐ ⊤
  ¬N∧ᴸ : ⁅ * ⁆̣               ▹ ∅ ⊢              (¬ 𝔞) ∧ 𝔞 ≋ₐ ⊥
  DM∧  : ⁅ * ⁆ ⁅ * ⁆̣         ▹ ∅ ⊢              ¬ (𝔞 ∧ 𝔟) ≋ₐ (¬ 𝔞) ∨ (¬ 𝔟)
  DM∨  : ⁅ * ⁆ ⁅ * ⁆̣         ▹ ∅ ⊢              ¬ (𝔞 ∨ 𝔟) ≋ₐ (¬ 𝔞) ∧ (¬ 𝔟)
  DM∀  : ⁅ N ⊩ * ⁆̣           ▹ ∅ ⊢       ¬ (∀′ (𝔞⟨ x₀ ⟩)) ≋ₐ ∃′ (¬ 𝔞⟨ x₀ ⟩)
  DM∃  : ⁅ N ⊩ * ⁆̣           ▹ ∅ ⊢       ¬ (∃′ (𝔞⟨ x₀ ⟩)) ≋ₐ ∀′ (¬ 𝔞⟨ x₀ ⟩)
  ∀D∧  : ⁅ N ⊩ * ⁆ ⁅ N ⊩ * ⁆̣ ▹ ∅ ⊢ ∀′ (𝔞⟨ x₀ ⟩ ∧ 𝔟⟨ x₀ ⟩) ≋ₐ (∀′ (𝔞⟨ x₀ ⟩)) ∧ (∀′ (𝔟⟨ x₀ ⟩))
  ∃D∨  : ⁅ N ⊩ * ⁆ ⁅ N ⊩ * ⁆̣ ▹ ∅ ⊢ ∃′ (𝔞⟨ x₀ ⟩ ∨ 𝔟⟨ x₀ ⟩) ≋ₐ (∃′ (𝔞⟨ x₀ ⟩)) ∨ (∃′ (𝔟⟨ x₀ ⟩))
  ∧P∀ᴸ : ⁅ * ⁆ ⁅ N ⊩ * ⁆̣     ▹ ∅ ⊢     𝔞 ∧ (∀′ (𝔟⟨ x₀ ⟩)) ≋ₐ ∀′ (𝔞 ∧ 𝔟⟨ x₀ ⟩)
  ∧P∃ᴸ : ⁅ * ⁆ ⁅ N ⊩ * ⁆̣     ▹ ∅ ⊢     𝔞 ∧ (∃′ (𝔟⟨ x₀ ⟩)) ≋ₐ ∃′ (𝔞 ∧ 𝔟⟨ x₀ ⟩)
  ∨P∀ᴸ : ⁅ * ⁆ ⁅ N ⊩ * ⁆̣     ▹ ∅ ⊢     𝔞 ∨ (∀′ (𝔟⟨ x₀ ⟩)) ≋ₐ ∀′ (𝔞 ∨ 𝔟⟨ x₀ ⟩)
  ∨P∃ᴸ : ⁅ * ⁆ ⁅ N ⊩ * ⁆̣     ▹ ∅ ⊢     𝔞 ∨ (∃′ (𝔟⟨ x₀ ⟩)) ≋ₐ ∃′ (𝔞 ∨ 𝔟⟨ x₀ ⟩)
  ∀Eᴸ  : ⁅ N ⊩ * ⁆ ⁅ N ⁆̣     ▹ ∅ ⊢           ∀′ (𝔞⟨ x₀ ⟩) ≋ₐ 𝔞⟨ 𝔟 ⟩ ∧ (∀′ (𝔞⟨ x₀ ⟩))
  ∃Eᴸ  : ⁅ N ⊩ * ⁆ ⁅ N ⁆̣     ▹ ∅ ⊢           ∃′ (𝔞⟨ x₀ ⟩) ≋ₐ 𝔞⟨ 𝔟 ⟩ ∨ (∃′ (𝔞⟨ x₀ ⟩))

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning

-- Derived equations
⊥U∨ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ∨ ⊥ ≋ 𝔞
⊥U∨ᴿ = tr (ax ∨C with《 𝔞 ◃ ⊥ 》) (ax ⊥U∨ᴸ with《 𝔞 》)
⊤U∧ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ∧ ⊤ ≋ 𝔞
⊤U∧ᴿ = tr (ax ∧C with《 𝔞 ◃ ⊤ 》) (ax ⊤U∧ᴸ with《 𝔞 》)
∧D∨ᴿ : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (𝔞 ∨ 𝔟) ∧ 𝔠 ≋ (𝔞 ∧ 𝔠) ∨ (𝔟 ∧ 𝔠)
∧D∨ᴿ = begin
  (𝔞 ∨ 𝔟) ∧ 𝔠       ≋⟨ ax ∧C with《 𝔞 ∨ 𝔟 ◃ 𝔠 》 ⟩
  𝔠 ∧ (𝔞 ∨ 𝔟)       ≋⟨ ax ∧D∨ᴸ with《 𝔠 ◃ 𝔞 ◃ 𝔟 》 ⟩
  (𝔠 ∧ 𝔞) ∨ (𝔠 ∧ 𝔟)  ≋⟨ cong₂[ ax ∧C with《 𝔠 ◃ 𝔞 》 ][ ax ∧C with《 𝔠 ◃ 𝔟 》 ]inside ◌ᵈ ∨ ◌ᵉ ⟩
  (𝔞 ∧ 𝔠) ∨ (𝔟 ∧ 𝔠)  ∎
⊥X∧ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ∧ ⊥ ≋ ⊥
⊥X∧ᴿ = tr (ax ∧C with《 𝔞 ◃ ⊥ 》) (ax ⊥X∧ᴸ with《 𝔞 》)
¬N∨ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ∨ (¬ 𝔞) ≋ ⊥
¬N∨ᴿ = tr (ax ∨C with《 𝔞 ◃ (¬ 𝔞) 》) (ax ¬N∨ᴸ with《 𝔞 》)
∨D∧ᴿ : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (𝔞 ∧ 𝔟) ∨ 𝔠 ≋ (𝔞 ∨ 𝔠) ∧ (𝔟 ∨ 𝔠)
∨D∧ᴿ = begin
  (𝔞 ∧ 𝔟) ∨ 𝔠       ≋⟨ ax ∨C with《 𝔞 ∧ 𝔟 ◃ 𝔠 》 ⟩
  𝔠 ∨ (𝔞 ∧ 𝔟)       ≋⟨ ax ∨D∧ᴸ with《 𝔠 ◃ 𝔞 ◃ 𝔟 》 ⟩
  (𝔠 ∨ 𝔞) ∧ (𝔠 ∨ 𝔟)  ≋⟨ cong₂[ ax ∨C with《 𝔠 ◃ 𝔞 》 ][ ax ∨C with《 𝔠 ◃ 𝔟 》 ]inside ◌ᵈ ∧ ◌ᵉ ⟩
  (𝔞 ∨ 𝔠) ∧ (𝔟 ∨ 𝔠)  ∎
⊤X∨ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ∨ ⊤ ≋ ⊤
⊤X∨ᴿ = tr (ax ∨C with《 𝔞 ◃ ⊤ 》) (ax ⊤X∨ᴸ with《 𝔞 》)
¬N∧ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ∧ (¬ 𝔞) ≋ ⊥
¬N∧ᴿ = tr (ax ∧C with《 𝔞 ◃ (¬ 𝔞) 》) (ax ¬N∧ᴸ with《 𝔞 》)
∧P∀ᴿ : ⁅ N ⊩ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (∀′ (𝔞⟨ x₀ ⟩)) ∧ 𝔟 ≋ ∀′ (𝔞⟨ x₀ ⟩ ∧ 𝔟)
∧P∀ᴿ = begin
  (∀′ (𝔞⟨ x₀ ⟩)) ∧ 𝔟   ≋⟨ ax ∧C with《 ∀′ (𝔞⟨ x₀ ⟩) ◃ 𝔟 》 ⟩
  𝔟 ∧ (∀′ (𝔞⟨ x₀ ⟩))   ≋⟨ ax ∧P∀ᴸ with《 𝔟 ◃ 𝔞⟨ x₀ ⟩ 》 ⟩
  ∀′ (𝔟 ∧ 𝔞⟨ x₀ ⟩)     ≋⟨ cong[ ax ∧C with《 𝔟 ◃ 𝔞⟨ x₀ ⟩ 》 ]inside ∀′ (◌ᶜ⟨ x₀ ⟩) ⟩
  ∀′ (𝔞⟨ x₀ ⟩ ∧ 𝔟)     ∎
∧P∃ᴿ : ⁅ N ⊩ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (∃′ (𝔞⟨ x₀ ⟩)) ∧ 𝔟 ≋ ∃′ (𝔞⟨ x₀ ⟩ ∧ 𝔟)
∧P∃ᴿ = begin
  (∃′ (𝔞⟨ x₀ ⟩)) ∧ 𝔟   ≋⟨ ax ∧C with《 ∃′ (𝔞⟨ x₀ ⟩) ◃ 𝔟 》 ⟩
  𝔟 ∧ (∃′ (𝔞⟨ x₀ ⟩))   ≋⟨ ax ∧P∃ᴸ with《 𝔟 ◃ 𝔞⟨ x₀ ⟩ 》 ⟩
  ∃′ (𝔟 ∧ 𝔞⟨ x₀ ⟩)     ≋⟨ cong[ ax ∧C with《 𝔟 ◃ 𝔞⟨ x₀ ⟩ 》 ]inside ∃′ (◌ᶜ⟨ x₀ ⟩) ⟩
  ∃′ (𝔞⟨ x₀ ⟩ ∧ 𝔟)     ∎
∨P∀ᴿ : ⁅ N ⊩ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (∀′ (𝔞⟨ x₀ ⟩)) ∨ 𝔟 ≋ ∀′ (𝔞⟨ x₀ ⟩ ∨ 𝔟)
∨P∀ᴿ = begin
  (∀′ (𝔞⟨ x₀ ⟩)) ∨ 𝔟   ≋⟨ ax ∨C with《 ∀′ (𝔞⟨ x₀ ⟩) ◃ 𝔟 》 ⟩
  𝔟 ∨ (∀′ (𝔞⟨ x₀ ⟩))   ≋⟨ ax ∨P∀ᴸ with《 𝔟 ◃ 𝔞⟨ x₀ ⟩ 》 ⟩
  ∀′ (𝔟 ∨ 𝔞⟨ x₀ ⟩)     ≋⟨ cong[ ax ∨C with《 𝔟 ◃ 𝔞⟨ x₀ ⟩ 》 ]inside ∀′ (◌ᶜ⟨ x₀ ⟩) ⟩
  ∀′ (𝔞⟨ x₀ ⟩ ∨ 𝔟)     ∎
∨P∃ᴿ : ⁅ N ⊩ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (∃′ (𝔞⟨ x₀ ⟩)) ∨ 𝔟 ≋ ∃′ (𝔞⟨ x₀ ⟩ ∨ 𝔟)
∨P∃ᴿ = begin
  (∃′ (𝔞⟨ x₀ ⟩)) ∨ 𝔟   ≋⟨ ax ∨C with《 ∃′ (𝔞⟨ x₀ ⟩) ◃ 𝔟 》 ⟩
  𝔟 ∨ (∃′ (𝔞⟨ x₀ ⟩))   ≋⟨ ax ∨P∃ᴸ with《 𝔟 ◃ 𝔞⟨ x₀ ⟩ 》 ⟩
  ∃′ (𝔟 ∨ 𝔞⟨ x₀ ⟩)     ≋⟨ cong[ ax ∨C with《 𝔟 ◃ 𝔞⟨ x₀ ⟩ 》 ]inside ∃′ (◌ᶜ⟨ x₀ ⟩) ⟩
  ∃′ (𝔞⟨ x₀ ⟩ ∨ 𝔟)     ∎
∀Eᴿ : ⁅ N ⊩ * ⁆ ⁅ N ⁆̣ ▹ ∅ ⊢ ∀′ (𝔞⟨ x₀ ⟩) ≋ (∀′ (𝔞⟨ x₀ ⟩)) ∧ 𝔞⟨ 𝔟 ⟩
∀Eᴿ = tr (ax ∀Eᴸ with《 𝔞⟨ x₀ ⟩ ◃ 𝔟 》) (ax ∧C with《  𝔞⟨ 𝔟 ⟩ ◃ ∀′ (𝔞⟨ x₀ ⟩) 》)
∃Eᴿ : ⁅ N ⊩ * ⁆ ⁅ N ⁆̣ ▹ ∅ ⊢ ∃′ (𝔞⟨ x₀ ⟩) ≋ (∃′ (𝔞⟨ x₀ ⟩)) ∨ 𝔞⟨ 𝔟 ⟩
∃Eᴿ = tr (ax ∃Eᴸ with《 𝔞⟨ x₀ ⟩ ◃ 𝔟 》) (ax ∨C with《  𝔞⟨ 𝔟 ⟩ ◃ ∃′ (𝔞⟨ x₀ ⟩) 》)
∃⟹ : ⁅ N ⊩ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (∃′ (𝔞⟨ x₀ ⟩)) ⟹ 𝔟 ≋ ∀′ (𝔞⟨ x₀ ⟩ ⟹ 𝔟)
∃⟹ = begin
  (∃′ (𝔞⟨ x₀ ⟩)) ⟹ 𝔟    ≡⟨⟩
  (¬ (∃′ (𝔞⟨ x₀ ⟩))) ∨ 𝔟 ≋⟨ cong[ ax DM∃ with《 𝔞⟨ x₀ ⟩ 》 ]inside (◌ᶜ ∨ 𝔟) ⟩
  (∀′ (¬ (𝔞⟨ x₀ ⟩))) ∨ 𝔟 ≋⟨ thm ∨P∀ᴿ with《 ¬ 𝔞⟨ x₀ ⟩ ◃ 𝔟 》 ⟩
  ∀′ (¬ (𝔞⟨ x₀ ⟩) ∨ 𝔟)   ≡⟨⟩
  ∀′ (𝔞⟨ x₀ ⟩ ⟹ 𝔟)      ∎
∀⟹ : ⁅ N ⊩ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (∀′ (𝔞⟨ x₀ ⟩)) ⟹ 𝔟 ≋ ∃′ (𝔞⟨ x₀ ⟩ ⟹ 𝔟)
∀⟹ = begin
  (∀′ (𝔞⟨ x₀ ⟩)) ⟹ 𝔟    ≡⟨⟩
  (¬ (∀′ (𝔞⟨ x₀ ⟩))) ∨ 𝔟 ≋⟨ cong[ ax DM∀ with《 𝔞⟨ x₀ ⟩ 》 ]inside (◌ᶜ ∨ 𝔟) ⟩
  (∃′ (¬ (𝔞⟨ x₀ ⟩))) ∨ 𝔟 ≋⟨ thm ∨P∃ᴿ with《 ¬ 𝔞⟨ x₀ ⟩ ◃ 𝔟 》 ⟩
  ∃′ (¬ (𝔞⟨ x₀ ⟩) ∨ 𝔟)   ≡⟨⟩
  ∃′ (𝔞⟨ x₀ ⟩ ⟹ 𝔟)      ∎
