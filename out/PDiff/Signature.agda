{-
This file was created from the following second-order syntax description:

type *T
  * : 0-ary

term PD
  add   : *  *  ->  * | _+_ r20
  mult  : *  *  ->  * | _×_ r40
  zero  : * | 𝟘 
  one   : * | 𝟙 
  neg   : *  ->  * | –_ r50
  pdiff : *.*  *  ->  * | ∂_∣_ 
-}

module PDiff.Signature where

open import SOAS.Context

-- Type declaration
data *T : Set where
  * : *T



open import SOAS.Syntax.Signature *T public
open import SOAS.Syntax.Build *T public

-- Operator symbols
data PDₒ : Set where
  addₒ multₒ zeroₒ oneₒ negₒ pdiffₒ : PDₒ

-- Term signature
PD:Sig : Signature PDₒ
PD:Sig = sig λ
  {  addₒ    → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  multₒ   → (⊢₀ *) , (⊢₀ *) ⟼₂ *
  ;  zeroₒ   → ⟼₀ *
  ;  oneₒ    → ⟼₀ *
  ;  negₒ    → (⊢₀ *) ⟼₁ *
  ;  pdiffₒ  → (* ⊢₁ *) , (⊢₀ *) ⟼₂ *
  }

open Signature PD:Sig public
