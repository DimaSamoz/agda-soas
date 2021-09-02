{-
This second-order signature was created from the following second-order syntax description:

syntax PropLog | PR

type
  * : 0-ary

term
  false : * | ⊥ 
  or    : *  *  ->  * | _∨_ l20
  true  : * | ⊤ 
  and   : *  *  ->  * | _∧_ l30
  not   : *  ->  * | ¬_ r50

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
  (DM∧) a b |> not (and (a, b)) = or  (not(a), not(b))
  (DM∨) a b |> not (or  (a, b)) = and (not(a), not(b))
-}

module PropLog.Signature where

open import SOAS.Context

open import SOAS.Common


open import SOAS.Syntax.Signature *T public
open import SOAS.Syntax.Build *T public

-- Operator symbols
data PRₒ : Set where
  falseₒ orₒ trueₒ andₒ notₒ : PRₒ

-- Term signature
PR:Sig : Signature PRₒ
PR:Sig = sig λ
  {  falseₒ  → ⟼₀ *
  ;  orₒ     → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  trueₒ   → ⟼₀ *
  ;  andₒ    → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  notₒ    → (⊢₀ *) ⟼₁ *
  }

open Signature PR:Sig public
