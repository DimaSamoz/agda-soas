{-
This second-order signature was created from the following second-order syntax description:

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

module PCF.Signature where

open import SOAS.Context

-- Type declaration
data PCFT : Set where
  N   : PCFT
  _↣_ : PCFT → PCFT → PCFT
  B   : PCFT
infixr 30 _↣_


open import SOAS.Syntax.Signature PCFT public
open import SOAS.Syntax.Build PCFT public

-- Operator symbols
data PCFₒ : Set where
  appₒ lamₒ : {α β : PCFT} → PCFₒ
  trₒ flₒ zeₒ suₒ prₒ izₒ : PCFₒ
  ifₒ fixₒ : {α : PCFT} → PCFₒ

-- Term signature
PCF:Sig : Signature PCFₒ
PCF:Sig = sig λ
  { (appₒ {α}{β}) → (⊢₀ α ↣ β) , (⊢₀ α) ⟼₂ β
  ; (lamₒ {α}{β}) → (α ⊢₁ β) ⟼₁ α ↣ β
  ;  trₒ          → ⟼₀ B
  ;  flₒ          → ⟼₀ B
  ;  zeₒ          → ⟼₀ N
  ;  suₒ          → (⊢₀ N) ⟼₁ N
  ;  prₒ          → (⊢₀ N) ⟼₁ N
  ;  izₒ          → (⊢₀ N) ⟼₁ B
  ; (ifₒ  {α})    → (⊢₀ B) , (⊢₀ α) , (⊢₀ α) ⟼₃ α
  ; (fixₒ {α})    → (α ⊢₁ α) ⟼₁ α
  }

open Signature PCF:Sig public
