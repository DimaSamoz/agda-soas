{-
This second-order signature was created from the following second-order syntax description:

syntax TLC | Λ

type
  N   : 0-ary
  _↣_ : 2-ary | r30
  𝟙   : 0-ary
  _⊗_ : 2-ary | l40
  𝟘   : 0-ary
  _⊕_ : 2-ary | l30

term
  app   : α ↣ β  α  ->  β | _$_ l20
  lam   : α.β  ->  α ↣ β | ƛ_ r10
  unit  : 𝟙
  pair  : α  β  ->  α ⊗ β | ⟨_,_⟩
  fst   : α ⊗ β  ->  α
  snd   : α ⊗ β  ->  β
  abort : 𝟘  ->  α
  inl   : α  ->  α ⊕ β
  inr   : β  ->  α ⊕ β
  case  : α ⊕ β  α.γ  β.γ  ->  γ
  ze    : N
  su    : N  ->  N
  nrec  : N  α  (α,N).α  ->  α

theory
  (ƛβ) b : α.β  a : α |> app (lam(x.b[x]), a) = b[a]
  (ƛη) f : α ↣ β      |> lam (x. app(f, x))   = f
  (𝟙η) u : 𝟙 |> u = unit
  (fβ) a : α  b : β |> fst (pair(a, b))      = a
  (sβ) a : α  b : β |> snd (pair(a, b))      = b
  (pη) p : α ⊗ β    |> pair (fst(p), snd(p)) = p
  (𝟘η) e : 𝟘  c : α |> abort(e) = c
  (lβ) a : α   f : α.γ  g : β.γ |> case (inl(a), x.f[x], y.g[y])      = f[a]
  (rβ) b : β   f : α.γ  g : β.γ |> case (inr(b), x.f[x], y.g[y])      = g[b]
  (cη) s : α ⊕ β  c : (α ⊕ β).γ |> case (s, x.c[inl(x)], y.c[inr(y)]) = c[s]
  (zeβ) z : α   s : (α,N).α        |> nrec (ze,       z, r m. s[r,m]) = z
  (suβ) z : α   s : (α,N).α  n : N |> nrec (su (n), z, r m. s[r,m]) = s[nrec (n, z, r m. s[r,m]), n]
  (ift) t f : α |> if (true, t, f) = t
  (iff) t f : α |> if (false, t, f) = f
-}

module TLC.Signature where

open import SOAS.Context

-- Type declaration
data ΛT : Set where
  N   : ΛT
  _↣_ : ΛT → ΛT → ΛT
  𝟙   : ΛT
  _⊗_ : ΛT → ΛT → ΛT
  𝟘   : ΛT
  _⊕_ : ΛT → ΛT → ΛT
infixr 30 _↣_
infixl 40 _⊗_
infixl 30 _⊕_

-- Derived types
B : ΛT
B = 𝟙 ⊕ 𝟙

open import SOAS.Syntax.Signature ΛT public
open import SOAS.Syntax.Build ΛT public

-- Operator symbols
data Λₒ : Set where
  appₒ lamₒ pairₒ fstₒ sndₒ inlₒ inrₒ : {α β : ΛT} → Λₒ
  unitₒ zeₒ suₒ : Λₒ
  abortₒ nrecₒ : {α : ΛT} → Λₒ
  caseₒ : {α β γ : ΛT} → Λₒ

-- Term signature
Λ:Sig : Signature Λₒ
Λ:Sig = sig λ
  { (appₒ   {α}{β})    → (⊢₀ α ↣ β) , (⊢₀ α) ⟼₂ β
  ; (lamₒ   {α}{β})    → (α ⊢₁ β) ⟼₁ α ↣ β
  ;  unitₒ             → ⟼₀ 𝟙
  ; (pairₒ  {α}{β})    → (⊢₀ α) , (⊢₀ β) ⟼₂ α ⊗ β
  ; (fstₒ   {α}{β})    → (⊢₀ α ⊗ β) ⟼₁ α
  ; (sndₒ   {α}{β})    → (⊢₀ α ⊗ β) ⟼₁ β
  ; (abortₒ {α})       → (⊢₀ 𝟘) ⟼₁ α
  ; (inlₒ   {α}{β})    → (⊢₀ α) ⟼₁ α ⊕ β
  ; (inrₒ   {α}{β})    → (⊢₀ β) ⟼₁ α ⊕ β
  ; (caseₒ  {α}{β}{γ}) → (⊢₀ α ⊕ β) , (α ⊢₁ γ) , (β ⊢₁ γ) ⟼₃ γ
  ;  zeₒ               → ⟼₀ N
  ;  suₒ               → (⊢₀ N) ⟼₁ N
  ; (nrecₒ  {α})       → (⊢₀ N) , (⊢₀ α) , (α , N ⊢₂ α) ⟼₃ α
  }

open Signature Λ:Sig public
