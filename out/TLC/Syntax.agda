{-
This second-order term syntax was created from the following second-order syntax description:

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


module TLC.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import TLC.Signature

private
  variable
    Γ Δ Π : Ctx
    α β γ : ΛT
    𝔛 : Familyₛ

-- Inductive term declaration
module Λ:Terms (𝔛 : Familyₛ) where

  data Λ : Familyₛ where
    var  : ℐ ⇾̣ Λ
    mvar : 𝔛 α Π → Sub Λ Π Γ → Λ α Γ

    _$_   : Λ (α ↣ β) Γ → Λ α Γ → Λ β Γ
    ƛ_    : Λ β (α ∙ Γ) → Λ (α ↣ β) Γ
    unit  : Λ 𝟙 Γ
    ⟨_,_⟩ : Λ α Γ → Λ β Γ → Λ (α ⊗ β) Γ
    fst   : Λ (α ⊗ β) Γ → Λ α Γ
    snd   : Λ (α ⊗ β) Γ → Λ β Γ
    abort : Λ 𝟘 Γ → Λ α Γ
    inl   : Λ α Γ → Λ (α ⊕ β) Γ
    inr   : Λ β Γ → Λ (α ⊕ β) Γ
    case  : Λ (α ⊕ β) Γ → Λ γ (α ∙ Γ) → Λ γ (β ∙ Γ) → Λ γ Γ
    ze    : Λ N Γ
    su    : Λ N Γ → Λ N Γ
    nrec  : Λ N Γ → Λ α Γ → Λ α (α ∙ N ∙ Γ) → Λ α Γ

  infixl 20 _$_
  infixr 10 ƛ_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Λᵃ : MetaAlg Λ
  Λᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (appₒ   ⅋ a , b)     → _$_   a b
      (lamₒ   ⅋ a)         → ƛ_    a
      (unitₒ  ⅋ _)         → unit
      (pairₒ  ⅋ a , b)     → ⟨_,_⟩ a b
      (fstₒ   ⅋ a)         → fst   a
      (sndₒ   ⅋ a)         → snd   a
      (abortₒ ⅋ a)         → abort a
      (inlₒ   ⅋ a)         → inl   a
      (inrₒ   ⅋ a)         → inr   a
      (caseₒ  ⅋ a , b , c) → case  a b c
      (zeₒ    ⅋ _)         → ze
      (suₒ    ⅋ a)         → su    a
      (nrecₒ  ⅋ a , b , c) → nrec  a b c
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Λᵃ = MetaAlg Λᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : Λ ⇾̣ 𝒜
    𝕊 : Sub Λ Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (_$_   a b)   = 𝑎𝑙𝑔 (appₒ   ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (ƛ_    a)     = 𝑎𝑙𝑔 (lamₒ   ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞  unit         = 𝑎𝑙𝑔 (unitₒ  ⅋ tt)
    𝕤𝕖𝕞 (⟨_,_⟩ a b)   = 𝑎𝑙𝑔 (pairₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (fst   a)     = 𝑎𝑙𝑔 (fstₒ   ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (snd   a)     = 𝑎𝑙𝑔 (sndₒ   ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (abort a)     = 𝑎𝑙𝑔 (abortₒ ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (inl   a)     = 𝑎𝑙𝑔 (inlₒ   ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (inr   a)     = 𝑎𝑙𝑔 (inrₒ   ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (case  a b c) = 𝑎𝑙𝑔 (caseₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b , 𝕤𝕖𝕞 c)
    𝕤𝕖𝕞  ze           = 𝑎𝑙𝑔 (zeₒ    ⅋ tt)
    𝕤𝕖𝕞 (su    a)     = 𝑎𝑙𝑔 (suₒ    ⅋ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (nrec  a b c) = 𝑎𝑙𝑔 (nrecₒ  ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b , 𝕤𝕖𝕞 c)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Λᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ Λ α Γ) → 𝕤𝕖𝕞 (Λᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (appₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (lamₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (unitₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (pairₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (fstₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (sndₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (abortₒ ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (inlₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (inrₒ   ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (caseₒ  ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (zeₒ    ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (suₒ    ⅋ _) = refl
      ⟨𝑎𝑙𝑔⟩ (nrecₒ  ⅋ _) = refl

      𝕊-tab : (mε : Π ~[ Λ ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : Λ ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Λᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : Λ α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub Λ Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (_$_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (ƛ_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! unit = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (⟨_,_⟩ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (fst a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (snd a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (abort a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (inl a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (inr a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (case a b c) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b | 𝕤𝕖𝕞! c = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! ze = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (su a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (nrec a b c) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b | 𝕤𝕖𝕞! c = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
Λ:Syn : Syntax
Λ:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = Λ:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open Λ:Terms 𝔛 in record
    { ⊥ = Λ ⋉ Λᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax Λ:Syn public
open Λ:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands Λᵃ public
open import SOAS.Metatheory Λ:Syn public

-- Derived operations
true : Λ 𝔛 B Γ
true = inl unit
false : Λ 𝔛 B Γ
false = inr unit
if : Λ 𝔛 B Γ → Λ 𝔛 α Γ → Λ 𝔛 α Γ → Λ 𝔛 α Γ
if b t e = case b (Theory.𝕨𝕜 _ t) (Theory.𝕨𝕜 _ e)

plus : Λ 𝔛 (N ↣ N ↣ N) Γ
plus = ƛ (ƛ (nrec x₁ x₀ (su x₀)))

uncurry : Λ 𝔛 ((α ↣ β ↣ γ) ↣ (α ⊗ β) ↣ γ) Γ
uncurry = ƛ ƛ x₁ $ fst x₀ $ snd x₀
