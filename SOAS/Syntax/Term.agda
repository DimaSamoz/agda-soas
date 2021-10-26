
import SOAS.Syntax.Signature as Sig
open import SOAS.Families.Core

-- Term syntax for a signature
module SOAS.Syntax.Term
  {T : Set}(open Sig T)
  {O : Set}(S : Signature O) where


open import SOAS.Syntax.Arguments {T}
open import SOAS.Metatheory.Syntax {T}

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Variable
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Abstract.Hom

open import Categories.Object.Initial

open import Data.List.Base using (List ; [] ; [_] ; _∷_)
open import Data.Unit

open Signature S

private
  variable
    α β τ : T
    Γ Δ Π : Ctx

module _ (𝔛 : Familyₛ) where
  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  -- Grammar of terms for a (⅀,𝔛)-meta-algebra
  data 𝕋 : Familyₛ where
    con  : ⅀ 𝕋 τ Γ → 𝕋 τ Γ
    var  : ℐ τ Γ → 𝕋 τ Γ
    mvar : 𝔛 τ Π → Sub 𝕋 Π Γ → 𝕋 τ Γ

  Tmᵃ : MetaAlg 𝕋
  Tmᵃ = record { 𝑎𝑙𝑔 = con ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 ε → mvar 𝔪 (tabulate ε) }

  -- 𝕋 is the initial meta-algebra
  𝕋:Init : Initial 𝕄etaAlgebras
  𝕋:Init = record
    { ⊥ = 𝕋 ⋉ Tmᵃ
    ; ⊥-is-initial = record
      { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → (𝕤𝕖𝕞 𝒜ᵃ) ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
      ; !-unique = λ { {𝒜 ⋉ 𝒜ᵃ}(g ⋉ gᵃ⇒) {x = t} →  𝕤𝕖𝕞! 𝒜ᵃ gᵃ⇒ t } } }
    where
    module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where
      open MetaAlg 𝒜ᵃ
      𝕤𝕖𝕞 : 𝕋 ⇾̣ 𝒜
      𝔸 : (as : List (Ctx × T)) → Arg as 𝕋 Γ → Arg as 𝒜 Γ
      𝔸 [] tt = tt
      𝔸 (_ ∷ []) t = 𝕤𝕖𝕞 t
      𝔸 (_ ∷ a ∷ as) (t , ts) = (𝕤𝕖𝕞 t , 𝔸 (a ∷ as) ts)
      𝕊 : Sub 𝕋 Π Γ → Π ~[ 𝒜 ]↝ Γ
      𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
      𝕊 (t ◂ σ) (old v) = 𝕊 σ v
      𝕤𝕖𝕞 (con (o ⋮ a)) = 𝑎𝑙𝑔 (o ⋮ 𝔸 (Arity o) a)
      𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v
      𝕤𝕖𝕞 (mvar 𝔪 ε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 ε)

      𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Tmᵃ 𝒜ᵃ 𝕤𝕖𝕞
      𝕤𝕖𝕞ᵃ⇒ = record
        { ⟨𝑎𝑙𝑔⟩ = λ{ {t = (o ⋮ a)} → cong (λ - → 𝑎𝑙𝑔 (o ⋮ -)) (𝔸-Arg₁ (Arity o) a) }
        ; ⟨𝑣𝑎𝑟⟩ = refl
        ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{ε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab ε)) }
        }
        where
        𝔸-Arg₁ : (as : List (Ctx × T))(a : Arg as 𝕋 Γ)
            → 𝔸 as a ≡ Arg₁ as 𝕤𝕖𝕞 a
        𝔸-Arg₁ [] tt = refl
        𝔸-Arg₁ (_ ∷ []) t = refl
        𝔸-Arg₁ (_ ∷ a ∷ as) (t , ap) = cong (_ ,_) (𝔸-Arg₁ (a ∷ as) ap)

        𝕊-tab : (ε : Π ~[ 𝕋 ]↝ Γ)(v : ℐ α Π)
              → 𝕊 (tabulate ε) v ≡ 𝕤𝕖𝕞 (ε v)
        𝕊-tab ε new = refl
        𝕊-tab ε (old v) = 𝕊-tab (ε ∘ old) v

      module _ {g : 𝕋 ⇾̣ 𝒜}(gᵃ⇒ : MetaAlg⇒ Tmᵃ 𝒜ᵃ g) where
        open MetaAlg⇒ gᵃ⇒

        𝕤𝕖𝕞! : (t : 𝕋 α Γ) → 𝕤𝕖𝕞 t ≡ g t
        𝕊-ix : (ε : Sub 𝕋 Π Γ)(v : ℐ α Π) → 𝕊 ε v ≡ g (index ε v)
        𝕊-ix (x ◂ ε) new = 𝕤𝕖𝕞! x
        𝕊-ix (x ◂ ε) (old v) = 𝕊-ix ε v
        𝔸-Arg₁ : (as : List (Ctx × T))(ar : Arg as 𝕋 Γ)
              → 𝔸 as ar ≡ Arg₁ as g ar
        𝔸-Arg₁ [] tt = refl
        𝔸-Arg₁ (_ ∷ []) t = 𝕤𝕖𝕞! t
        𝔸-Arg₁ (_ ∷ a ∷ as) (t , ap) = cong₂ _,_ (𝕤𝕖𝕞! t) (𝔸-Arg₁ (a ∷ as) ap)

        𝕤𝕖𝕞! (con (o ⋮ a)) rewrite 𝔸-Arg₁ (Arity o) a = sym ⟨𝑎𝑙𝑔⟩
        𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩
        𝕤𝕖𝕞! (mvar 𝔪 ε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix ε)) =
          trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id ε))

-- Syntax instance for a term grammar
𝕋:Syn : Syntax
𝕋:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; 𝕋:Init = 𝕋:Init
  ; mvarᵢ = mvar }
