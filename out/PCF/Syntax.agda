{-
This second-order term syntax was created from the following second-order syntax description:

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


module PCF.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import PCF.Signature

private
  variable
    Γ Δ Π : Ctx
    α β : PCFT
    𝔛 : Familyₛ

-- Inductive term declaration
module PCF:Terms (𝔛 : Familyₛ) where

  data PCF : Familyₛ where
    var  : ℐ ⇾̣ PCF
    mvar : 𝔛 α Π → Sub PCF Π Γ → PCF α Γ

    _$_ : PCF (α ↣ β) Γ → PCF α Γ → PCF β Γ
    ƛ_  : PCF β (α ∙ Γ) → PCF (α ↣ β) Γ
    tr  : PCF B Γ
    fl  : PCF B Γ
    ze  : PCF N Γ
    su  : PCF N Γ → PCF N Γ
    pr  : PCF N Γ → PCF N Γ
    0?  : PCF N Γ → PCF B Γ
    if  : PCF B Γ → PCF α Γ → PCF α Γ → PCF α Γ
    fix : PCF α (α ∙ Γ) → PCF α Γ

  infixl 20 _$_
  infixr 10 ƛ_

  open import SOAS.Metatheory.SynAlgebra ⅀F 𝔛

  PCFᵃ : SynAlg PCF
  PCFᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (appₒ ⋮ a , b)     → _$_ a b
      (lamₒ ⋮ a)         → ƛ_  a
      (trₒ  ⋮ _)         → tr
      (flₒ  ⋮ _)         → fl
      (zeₒ  ⋮ _)         → ze
      (suₒ  ⋮ a)         → su  a
      (prₒ  ⋮ a)         → pr  a
      (izₒ  ⋮ a)         → 0?  a
      (ifₒ  ⋮ a , b , c) → if  a b c
      (fixₒ ⋮ a)         → fix a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module PCFᵃ = SynAlg PCFᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : SynAlg 𝒜) where

    open SynAlg 𝒜ᵃ

    𝕤𝕖𝕞 : PCF ⇾̣ 𝒜
    𝕊 : Sub PCF Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (_$_ a b)   = 𝑎𝑙𝑔 (appₒ ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (ƛ_  a)     = 𝑎𝑙𝑔 (lamₒ ⋮ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞  tr         = 𝑎𝑙𝑔 (trₒ  ⋮ tt)
    𝕤𝕖𝕞  fl         = 𝑎𝑙𝑔 (flₒ  ⋮ tt)
    𝕤𝕖𝕞  ze         = 𝑎𝑙𝑔 (zeₒ  ⋮ tt)
    𝕤𝕖𝕞 (su  a)     = 𝑎𝑙𝑔 (suₒ  ⋮ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (pr  a)     = 𝑎𝑙𝑔 (prₒ  ⋮ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (0?  a)     = 𝑎𝑙𝑔 (izₒ  ⋮ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (if  a b c) = 𝑎𝑙𝑔 (ifₒ  ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b , 𝕤𝕖𝕞 c)
    𝕤𝕖𝕞 (fix a)     = 𝑎𝑙𝑔 (fixₒ ⋮ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : SynAlg⇒ PCFᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ PCF α Γ) → 𝕤𝕖𝕞 (PCFᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (appₒ ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (lamₒ ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (trₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (flₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (zeₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (suₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (prₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (izₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (ifₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (fixₒ ⋮ _) = refl

      𝕊-tab : (mε : Π ~[ PCF ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : PCF ⇾̣ 𝒜)(gᵃ⇒ : SynAlg⇒ PCFᵃ 𝒜ᵃ g) where

      open SynAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : PCF α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub PCF Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (_$_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (ƛ_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! tr = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! fl = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! ze = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (su a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (pr a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (0? a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (if a b c) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b | 𝕤𝕖𝕞! c = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (fix a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
PCF:Syn : Syntax
PCF:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = PCF:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open PCF:Terms 𝔛 in record
    { ⊥ = PCF ⋉ PCFᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax PCF:Syn public
open PCF:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands PCFᵃ public
open import SOAS.Metatheory PCF:Syn public
