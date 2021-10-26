{-
This second-order term syntax was created from the following second-order syntax description:

syntax Lens | L

type
  S : 0-ary
  A : 0-ary

term
  get : S  ->  A
  put : S  A  ->  S

theory
  (PG) s : S  a : A   |> get (put (s, a))   = a
  (GP) s : S          |> put (s, get(s))    = s
  (PP) s : S  a b : A |> put (put(s, a), b) = put (s, a)
-}


module Lens.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import Lens.Signature

private
  variable
    Γ Δ Π : Ctx
    α : LT
    𝔛 : Familyₛ

-- Inductive term declaration
module L:Terms (𝔛 : Familyₛ) where

  data L : Familyₛ where
    var  : ℐ ⇾̣ L
    mvar : 𝔛 α Π → Sub L Π Γ → L α Γ

    get : L S Γ → L A Γ
    put : L S Γ → L A Γ → L S Γ



  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Lᵃ : MetaAlg L
  Lᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (getₒ ⋮ a)     → get a
      (putₒ ⋮ a , b) → put a b
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Lᵃ = MetaAlg Lᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : L ⇾̣ 𝒜
    𝕊 : Sub L Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 (get a)   = 𝑎𝑙𝑔 (getₒ ⋮ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (put a b) = 𝑎𝑙𝑔 (putₒ ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Lᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ L α Γ) → 𝕤𝕖𝕞 (Lᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (getₒ ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (putₒ ⋮ _) = refl

      𝕊-tab : (mε : Π ~[ L ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : L ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Lᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : L α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub L Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! (get a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (put a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
L:Syn : Syntax
L:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = L:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open L:Terms 𝔛 in record
    { ⊥ = L ⋉ Lᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax L:Syn public
open L:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands Lᵃ public
open import SOAS.Metatheory L:Syn public
