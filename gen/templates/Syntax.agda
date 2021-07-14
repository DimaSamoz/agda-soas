{-
This file was created from the following second-order syntax description:

$sig_string
-}

module ${syn_name}.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import ${syn_name}.Signature

private
  variable
    Γ Δ Π : Ctx
    $ty_vars : $type

-- Inductive term declaration
module ${sig}:Syntax (𝔛 : Familyₛ) where

  data ${sig} : Familyₛ where
    var  : ℐ ⇾̣ ${sig}
    mvar : 𝔛 $fst_ty_var Π → Sub ${sig} Π Γ → ${sig} $fst_ty_var Γ

    $syn_constructors

  $op_fixity

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  ${sig}ᵃ : MetaAlg ${sig}
  ${sig}ᵃ = record
    { 𝑎𝑙𝑔 = λ where
      $alg_patterns
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module ${sig}ᵃ = MetaAlg ${sig}ᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : ${sig} ⇾̣ 𝒜
    𝕊 : Sub ${sig} Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞 $sem_patterns

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ ${sig}ᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ ${sig} $fst_ty_var Γ) → 𝕤𝕖𝕞 (${sig}ᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ $alg_hom_patterns

      𝕊-tab : (mε : Π ~[ ${sig} ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : ${sig} ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ ${sig}ᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : ${sig} $fst_ty_var Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub ${sig} Π Γ)(v : ℐ $fst_ty_var Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! $alg_unique_patterns


-- Syntax instance for the signature
${sig}:Syn : Syntax
${sig}:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = ${sig}:Syntax.mvar
  ; 𝕋:Init = λ 𝔛 → let open ${sig}:Syntax 𝔛 in record
    { ⊥ = ${sig} ⋉ ${sig}ᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

open Syntax $sig:Syn public

-- Working area
open ${sig}:Syntax
open import SOAS.Families.Build
open import SOAS.Syntax.Shorthands ${sig}ᵃ
