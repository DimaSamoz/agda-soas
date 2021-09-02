{-
This second-order signature was created from the following second-order syntax description:

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
  (∨B∧ᴸ) a b |> or (and (a, b), a) = a
  (∨B∧ᴿ) a b |> or (a, and (a, b)) = a
  (∧B∨ᴸ) a b |> and (or (a, b), a) = a
  (∧B∨ᴿ) a b |> and (a, or (a, b)) = a  
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

module FOL.Signature where

open import SOAS.Context

-- Type declaration
data FOLT : Set where
  * : FOLT
  N : FOLT



open import SOAS.Syntax.Signature FOLT public
open import SOAS.Syntax.Build FOLT public

-- Operator symbols
data FOLₒ : Set where
  falseₒ orₒ trueₒ andₒ notₒ eqₒ allₒ exₒ : FOLₒ

-- Term signature
FOL:Sig : Signature FOLₒ
FOL:Sig = sig λ
  {  falseₒ  → ⟼₀ *
  ;  orₒ     → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  trueₒ   → ⟼₀ *
  ;  andₒ    → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  notₒ    → (⊢₀ *) ⟼₁ *
  ;  eqₒ     → (⊢₀ N) , (⊢₀ N) ⟼₂ *
  ;  allₒ    → (N ⊢₁ *) ⟼₁ *
  ;  exₒ     → (N ⊢₁ *) ⟼₁ *
  }

open Signature FOL:Sig public
