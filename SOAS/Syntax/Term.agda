
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
      𝕤𝕖𝕞 (con (o ⅋ a)) = 𝑎𝑙𝑔 (o ⅋ 𝔸 (Arity o) a)
      𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v
      𝕤𝕖𝕞 (mvar 𝔪 ε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 ε)

      𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Tmᵃ 𝒜ᵃ 𝕤𝕖𝕞
      𝕤𝕖𝕞ᵃ⇒ = record
        { ⟨𝑎𝑙𝑔⟩ = λ{ {t = (o ⅋ a)} → cong (λ - → 𝑎𝑙𝑔 (o ⅋ -)) (𝔸-Arg₁ (Arity o) a) }
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

        𝕤𝕖𝕞! (con (o ⅋ a)) rewrite 𝔸-Arg₁ (Arity o) a = sym ⟨𝑎𝑙𝑔⟩
        𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩
        𝕤𝕖𝕞! (mvar 𝔪 ε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix ε)) =
          trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tabix∘≈id ε))

-- Syntax instance for a term grammar
𝕋:Syn : Syntax
𝕋:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; 𝕋:Init = 𝕋:Init
  ; mvarᵢ = mvar }

      -- !-AP! (Arity o) ar = sym ⟨𝑎𝑙𝑔⟩
      --       !-unique (var v) = sym ⟨𝑣𝑎𝑟⟩
      --       !-unique (mvar 𝔪 ε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (!-Sub! ε) )
      --         = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tabix∘≈id ε))
-- 𝕋:Init = record
--   { ⊥ = 𝕋 ⋉ Tmᵃ
--   ; ⊥-is-initial = record
--     { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → (! 𝒜ᵃ) ⋉ !ᵃ⇒ 𝒜ᵃ }
--     ; 𝕤𝕖𝕞! = λ { {𝒜 ⋉ 𝒜ᵃ}(f ⋉ fᵃ⇒) {x = t} → !-unique 𝒜ᵃ fᵃ⇒ t } }
--   }
--   where
--   open M.MetaAlg
--   ! : {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) → 𝕋 ⇾̣ 𝒜
--   ! 𝒜ᵃ (con (o , e , ar)) = 𝑎𝑙𝑔 𝒜ᵃ (o , e , (λ a → ! 𝒜ᵃ (ar a)))
--   ! 𝒜ᵃ (var v)            = 𝑣𝑎𝑟 𝒜ᵃ v
--   ! 𝒜ᵃ (mvar 𝔪 ε)         = 𝑚𝑣𝑎𝑟 𝒜ᵃ 𝔪 (λ p → ! 𝒜ᵃ (ε p))
--
--   !ᵃ⇒ : {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) → M.MetaAlg⇒ Tmᵃ 𝒜ᵃ (! 𝒜ᵃ)
--   !ᵃ⇒ 𝒜ᵃ = record { ⟨𝑎𝑙𝑔⟩ = refl ; ⟨𝑣𝑎𝑟⟩ = refl ; ⟨𝑚𝑣𝑎𝑟⟩ = refl }
--
--   open M.MetaAlg⇒
--   open ≡-Reasoning
--   !-unique : {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜){g : 𝕋 ⇾̣ 𝒜}
--              (gᵃ⇒ : M.MetaAlg⇒ Tmᵃ 𝒜ᵃ g)(t : 𝕋 α Γ)
--            → ! 𝒜ᵃ t ≡ g t
--   !-unique 𝒜ᵃ {g} gᵃ⇒ (con (o , refl , af)) = begin
--         𝑎𝑙𝑔 𝒜ᵃ (o , refl , (λ a → ! 𝒜ᵃ (af a)))
--     ≡⟨ congr (cong (refl ,_) (iext (dext λ y → !-unique 𝒜ᵃ gᵃ⇒ (af y))))
--              (λ - → 𝑎𝑙𝑔 𝒜ᵃ (o , -))⟩
--         𝑎𝑙𝑔 𝒜ᵃ (o , refl , (λ a → g (af a)))
--     ≡˘⟨ ⟨𝑎𝑙𝑔⟩ gᵃ⇒ ⟩
--         g (con (o , refl , af))
--     ∎
--   !-unique 𝒜ᵃ gᵃ⇒ (var x) = sym (⟨𝑣𝑎𝑟⟩ gᵃ⇒)
--   !-unique 𝒜ᵃ {g} gᵃ⇒ (mvar 𝔪 ε) = begin
--     𝑚𝑣𝑎𝑟 𝒜ᵃ 𝔪 (λ p → ! 𝒜ᵃ (ε p)) ≡⟨ congr (dext (λ p → !-unique 𝒜ᵃ gᵃ⇒ (ε p)))
--                                            (𝑚𝑣𝑎𝑟 𝒜ᵃ 𝔪) ⟩
--     𝑚𝑣𝑎𝑟 𝒜ᵃ 𝔪 (λ x → g (ε x))    ≡˘⟨ ⟨𝑚𝑣𝑎𝑟⟩ gᵃ⇒ ⟩
--     g (mvar 𝔪 ε)                 ∎
--
--
-- 𝕋:⇓Init : Initial M⇓.𝕄etaAlgebras
-- 𝕋:⇓Init = pres-Initial M≃M⇓ 𝕋:Init
--
-- -- module Shorthands where
-- --
-- --   _⟅–⟆ : 𝔛 α Γ → 𝕋 α Γ
-- --   𝔪 ⟅–⟆ = mvar 𝔪 var
-- --
-- --   _⟅⟆ : 𝔛 α ∅ → 𝕋 α Δ
-- --   𝔪 ⟅⟆ = mvar 𝔪 λ ()
-- --
-- --   _⟅_⟆ : 𝔛 α (β ∙ ∅)  → 𝕋 β Δ → 𝕋 α Δ
-- --   𝔪 ⟅ t ⟆ = mvar 𝔪 (λ{ new → t})
-- --
-- --   _⟅_≀_⟆ : {γ : T} → 𝔛 α (β ∙ γ ∙ ∅) → 𝕋 β Δ → 𝕋 γ Δ → 𝕋 α Δ
-- --   𝔪 ⟅ t ≀ s ⟆ = mvar  𝔪 (λ{ new → t ; (old new) → s})
-- --
-- --   _⟅_≀_≀_⟆ : {γ δ : T} → 𝔛 α (β ∙ γ ∙ δ ∙ ∅) → 𝕋 β Δ → 𝕋 γ Δ → 𝕋 δ Δ → 𝕋 α Δ
-- --   𝔪 ⟅ t ≀ s ≀ u ⟆ = mvar 𝔪 (λ{ new → t ; (old new) → s ; (old (old new)) → u })
--
-- -- record
-- --   { ⊥ = 𝕋 ⋉ Tm⇓ᵃ
-- --   ; ⊥-is-initial = record
-- --     { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → (! 𝒜ᵃ) ⋉ !ᵃ⇒ 𝒜ᵃ }
-- --     ; !-unique = λ { {𝒜 ⋉ 𝒜ᵃ}(f ⋉ fᵃ⇒) {x = t} → !-unique 𝒜ᵃ fᵃ⇒ t } }
-- --   }
-- --   where
-- --   open M⇓.MetaAlg
-- --   open ≡-Reasoning
-- --   ! : {𝒜 : Familyₛ}(𝒜⇓ᵃ : M⇓.MetaAlg 𝒜) → 𝕋 ⇾̣ 𝒜
-- --   ! 𝒜⇓ᵃ (con (o , e , ar)) = 𝑎𝑙𝑔 𝒜⇓ᵃ (o , e , AM→AP (Arity o) (λ a → ! 𝒜⇓ᵃ (ar a)))
-- --   ! 𝒜⇓ᵃ (var x) = 𝑣𝑎𝑟 𝒜⇓ᵃ x
-- --   ! 𝒜⇓ᵃ (mvar x x₁) = 𝑚𝑣𝑎𝑟 𝒜⇓ᵃ x (λ z → ! 𝒜⇓ᵃ (x₁ z))
-- --
-- --   !ᵃ⇒ : {𝒜 : Familyₛ}(𝒜⇓ᵃ : M⇓.MetaAlg 𝒜) → M⇓.MetaAlg⇒ Tm⇓ᵃ 𝒜⇓ᵃ (! 𝒜⇓ᵃ)
-- --   !ᵃ⇒ 𝒜⇓ᵃ = record
-- --     { ⟨𝑎𝑙𝑔⟩ = λ{ {t = (o , e , ar)} → cong (λ - → 𝑎𝑙𝑔 𝒜⇓ᵃ (o , e , -)) (begin
-- --           AM→AP (Arity o) (λ a → ! 𝒜⇓ᵃ (AP→AM (Arity o) ar a))
-- --       ≡⟨ AM→AP-commute (Arity o) (! 𝒜⇓ᵃ) (AP→AM (Arity o) ar) ⟩
-- --           ArgProd₁ (Arity o) (! 𝒜⇓ᵃ) (AM→AP (Arity o) (AP→AM (Arity o) ar))
-- --       ≡⟨ cong (ArgProd₁ (Arity o) (! 𝒜⇓ᵃ)) (P→M→P (Arity o) ar) ⟩
-- --           ArgProd₁ (Arity o) (! 𝒜⇓ᵃ) ar
-- --       ∎)  }
-- --     ; ⟨𝑣𝑎𝑟⟩ = refl
-- --     ; ⟨𝑚𝑣𝑎𝑟⟩ = refl }
-- --
-- --   open M⇓.MetaAlg⇒
-- --   !-unique : {𝒜 : Familyₛ}(𝒜⇓ᵃ : M⇓.MetaAlg 𝒜){g : 𝕋 ⇾̣ 𝒜}
-- --              (g⇓ᵃ⇒ : M⇓.MetaAlg⇒ Tm⇓ᵃ 𝒜⇓ᵃ g)(t : 𝕋 α Γ)
-- --            → ! 𝒜⇓ᵃ t ≡ g t
-- --   !-unique 𝒜⇓ᵃ {g} gᵃ⇒ (con (o , e , ar)) = begin
-- --         𝑎𝑙𝑔 𝒜⇓ᵃ (o , e , AM→AP (Arity o) (λ a → ! 𝒜⇓ᵃ (ar a)))
-- --     ≡⟨ cong (λ - → 𝑎𝑙𝑔 𝒜⇓ᵃ (o , e , -)) (cong (AM→AP (Arity o)) (iext (dext (λ a → !-unique 𝒜⇓ᵃ gᵃ⇒ (ar a))))) ⟩
-- --         𝑎𝑙𝑔 𝒜⇓ᵃ (o , e , AM→AP (Arity o) (λ a → g (ar a)))
-- --     ≡⟨ cong (λ - → 𝑎𝑙𝑔 𝒜⇓ᵃ (o , e , -)) (AM→AP-commute (Arity o) g ar) ⟩
-- --         𝑎𝑙𝑔 𝒜⇓ᵃ (o , e , ArgProd₁ (Arity o) g (AM→AP (Arity o) ar))
-- --     ≡˘⟨ ⟨𝑎𝑙𝑔⟩ gᵃ⇒ ⟩
-- --         g (con (o , e , AP→AM {𝕋} (Arity o) (AM→AP (Arity o) ar)))
-- --     ≡⟨ cong (λ { - → g (con (o , -)) }) (cong (e ,_) (iext (dext (M→P→M (Arity o) ar)))) ⟩
-- --         g (con (o , e , ar))
-- --     ∎
-- --   !-unique 𝒜⇓ᵃ {g} gᵃ⇒ (var x) = sym (⟨𝑣𝑎𝑟⟩ gᵃ⇒)
-- --   !-unique 𝒜⇓ᵃ {g} gᵃ⇒ (mvar 𝔪 ε) = begin
-- --         𝑚𝑣𝑎𝑟 𝒜⇓ᵃ 𝔪 (λ p → ! 𝒜⇓ᵃ (ε p))
-- --     ≡⟨ cong (𝑚𝑣𝑎𝑟 𝒜⇓ᵃ 𝔪) (dext (λ p → !-unique 𝒜⇓ᵃ gᵃ⇒ (ε p))) ⟩
-- --         𝑚𝑣𝑎𝑟 𝒜⇓ᵃ 𝔪 (g ∘ ε)
-- --     ≡˘⟨ ⟨𝑚𝑣𝑎𝑟⟩ gᵃ⇒ ⟩
-- --         g (mvar 𝔪 ε)
-- --     ∎
--
-- -- module 𝕋:Theory where
-- --   open Trav ⅀F ⅀:Str 𝔛 𝕋:Init public
-- --   open Ren ⅀F ⅀:Str 𝔛 𝕋:Init public
-- --   open Subst ⅀F ⅀:Str 𝔛 𝕋:Init public
-- --   open SOAS.Metatheory.Monoid ⅀F ⅀:Str
-- --   -- open SOAS.Metatheory.FreeMonoid ⅀F ⅀:Str public
-- --   open Semantics public
--
-- module 𝕋:⇓Theory where
--   open Trav ⅀⇓F ⅀⇓:Str 𝔛 𝕋:⇓Init public
--   open Ren ⅀⇓F ⅀⇓:Str 𝔛 𝕋:⇓Init public
--   open Subst ⅀⇓F ⅀⇓:Str 𝔛 𝕋:⇓Init public
--   open SOAS.Metatheory.Monoid ⅀⇓F ⅀⇓:Str
--   open Semantics public -- renaming (ᵃ⇒ to 𝕤𝕖𝕞ᵃ⇒)
--
--
-- data TTm : Familyₛ where
--   con : ⅀⇓ (TTm) τ Γ → TTm τ Γ
--   var  : ℐ τ Γ → TTm τ Γ
--   mvar : 𝔛 τ Π → Sub TTm Π Γ → TTm τ Γ
--
-- TTmᵃ : M⇓.MetaAlg TTm
-- TTmᵃ = record { 𝑎𝑙𝑔 = con ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 ε → mvar 𝔪 (tabulate ε) }
--
-- TTm:Init : Initial M⇓.𝕄etaAlgebras
-- TTm:Init = record
--   { ⊥ = TTm ⋉ TTmᵃ
--   ; ⊥-is-initial = record
--     { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → ! 𝒜ᵃ ⋉ !ᵃ⇒ 𝒜ᵃ }
--     ; !-unique = λ { {𝒜 ⋉ 𝒜ᵃ}(f ⋉ fᵃ⇒) {x = t} → !-unique 𝒜ᵃ fᵃ⇒ t }
--     }
--   }
--   where
--   module _ {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) where
--     open M⇓.MetaAlg 𝒜ᵃ
--     ! : TTm ⇾̣ 𝒜
--     !-Sub : Sub TTm Π Γ → Π ~[ 𝒜 ]↝ Γ
--     !-Sub (x ◂ σ) new = ! x
--     !-Sub (x ◂ σ) (old v) = !-Sub σ v
--     !-AP : (as : List (Ctx × T)) → ArgProd as TTm Γ → ArgProd as 𝒜 Γ
--     !-AP [] tt = tt
--     !-AP ((Θ , τ) ∷ as) (t , ap) = ! t , !-AP as ap
--
--     ! (con (o , refl , ar)) = 𝑎𝑙𝑔 (o , (refl , !-AP (Arity o) ar))
--     ! (var v) = 𝑣𝑎𝑟 v
--     ! (mvar 𝔪 ε) = 𝑚𝑣𝑎𝑟 𝔪 (!-Sub ε)
--
--     !AP-ArgProd₁ : (as : List (Ctx × T))(ar : ArgProd as TTm Γ)
--         → !-AP as ar ≡ ArgProd₁ as ! ar
--     !AP-ArgProd₁ [] tt = refl
--     !AP-ArgProd₁ ((Θ , τ) ∷ as) (t , ap) = cong (_ ,_) (!AP-ArgProd₁ as ap)
--
--     !ᵃ⇒ : M⇓.MetaAlg⇒ TTmᵃ 𝒜ᵃ !
--     !ᵃ⇒ = record
--       { ⟨𝑎𝑙𝑔⟩ = λ{ {t = (o , refl , ar)} → cong (λ - → 𝑎𝑙𝑔 (o , refl , -)) (!AP-ArgProd₁ (Arity o) ar) }
--       ; ⟨𝑣𝑎𝑟⟩ = refl
--       ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{ε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (⟨𝑚𝑣𝑎𝑟⟩ ε)) }
--       }
--       where
--       ⟨𝑚𝑣𝑎𝑟⟩ : (ε : Π ~[ TTm ]↝ Γ)(v : ℐ α Π)
--             → !-Sub (tabulate ε) v ≡ ! (ε v)
--       ⟨𝑚𝑣𝑎𝑟⟩ ε new = refl
--       ⟨𝑚𝑣𝑎𝑟⟩ ε (old v) = ⟨𝑚𝑣𝑎𝑟⟩ (ε ∘ old) v
--
--     module _ {g : TTm ⇾̣ 𝒜} (gᵃ⇒ : M⇓.MetaAlg⇒ TTmᵃ 𝒜ᵃ g) where
--
--
--
--       open M⇓.MetaAlg⇒ gᵃ⇒
--       open ≡-Reasoning
--       !-unique : (t : TTm α Γ) → ! t ≡ g t
--       !-Sub! : (ε : Sub TTm Π Γ)(v : ℐ α Π) → !-Sub ε v ≡ g (index ε v)
--       !-Sub! (x ◂ ε) new = !-unique x
--       !-Sub! (x ◂ ε) (old v) = !-Sub! ε v
--       !-AP! : (as : List (Ctx × T))(ar : ArgProd as TTm Γ)
--             → !-AP as ar ≡ ArgProd₁ as g ar
--       !-AP! [] tt = refl
--       !-AP! ((Θ , τ) ∷ as) (t , ap) = cong₂ _,_ (!-unique t) (!-AP! as ap)
--
--       !-unique (con (o , refl , ar)) rewrite !-AP! (Arity o) ar = sym ⟨𝑎𝑙𝑔⟩
--       !-unique (var v) = sym ⟨𝑣𝑎𝑟⟩
--       !-unique (mvar 𝔪 ε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (!-Sub! ε) )
--         = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tabix∘≈id ε))
--
-- -- 𝕋:Init = record
-- --   { ⊥ = 𝕋 ⋉ Tmᵃ
-- --   ; ⊥-is-initial = record
-- --     { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → (! 𝒜ᵃ) ⋉ !ᵃ⇒ 𝒜ᵃ }
-- --     ; !-unique = λ { {𝒜 ⋉ 𝒜ᵃ}(f ⋉ fᵃ⇒) {x = t} → !-unique 𝒜ᵃ fᵃ⇒ t } }
-- --   }
--
-- data CTm′ : Size → Familyₛ where
--   con⇓ : ⅀⇓ (CTm′ s) τ Γ → CTm′ (↑ s) τ Γ
--   var  : ℐ τ Γ → CTm′ (↑ s) τ Γ
--   mvar : 𝔛 τ Π → Sub (CTm′ s) Π Γ → CTm′ (↑ s) τ Γ
--
-- -- module CTM:Theory {𝒜 : Familyₛ} (𝒜ᵃ : M⇓.MetaAlg 𝒜) where
-- --
-- --   open M⇓.MetaAlg 𝒜ᵃ
-- --   𝕤𝕖𝕞 : CTM ⇾̣ 𝒜
-- --   𝕤𝕖𝕞-Sub : Sub CTM Π Γ → Π ~[ 𝒜 ]↝ Γ
-- --   𝕤𝕖𝕞-Sub (x ◂ σ) new = 𝕤𝕖𝕞 x
-- --   𝕤𝕖𝕞-Sub (x ◂ σ) (old v) = 𝕤𝕖𝕞-Sub σ v
-- --   𝕤𝕖𝕞-AP : (as : List (Ctx × T)) → ArgProd as CTM Γ → ArgProd as 𝒜 Γ
-- --   𝕤𝕖𝕞-AP [] tt = tt
-- --   𝕤𝕖𝕞-AP ((Θ , τ) ∷ as) (t , ap) = 𝕤𝕖𝕞 t , 𝕤𝕖𝕞-AP as ap
-- --
-- --   𝕤𝕖𝕞 (con (o , e , ar)) = 𝑎𝑙𝑔 (o , e , 𝕤𝕖𝕞-AP (Arity o) ar) --𝑎𝑙𝑔 (o , e , ArgProd₁ (Arity o) 𝕤𝕖𝕞 ar)
-- --   𝕤𝕖𝕞 (var x) = 𝑣𝑎𝑟 x
-- --   𝕤𝕖𝕞 (mvar 𝔪 ε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕤𝕖𝕞-Sub ε)
--   -- 𝕤𝕖𝕞 (con⇓ (o , e , ar)) = 𝑎𝑙𝑔 (o , e , λ a → 𝕤𝕖𝕞 (AP→AM (Arity o) ar a))
--   -- 𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v
--   -- 𝕤𝕖𝕞 (mvar 𝔪 ε) = 𝑚𝑣𝑎𝑟 𝔪 (λ p → 𝕤𝕖𝕞 (index ε p))
--
-- CTm : Familyₛ
-- CTm = CTm′ ∞
--
-- CTm⇓ᵃ : M⇓.MetaAlg CTm
-- CTm⇓ᵃ = record { 𝑎𝑙𝑔 = con⇓ ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 ε → mvar 𝔪 (tabulate ε) }
--
-- CTmᵃ : MetaAlg CTm
-- CTmᵃ = M⇓→M CTm⇓ᵃ
--
-- module CTm:Theory {𝒜 : Familyₛ} (𝒜ᵃ : MetaAlg 𝒜) where
--
--   open MetaAlg 𝒜ᵃ
--   𝕤𝕖𝕞 : CTm′ s ⇾̣ 𝒜
--   𝕤𝕖𝕞 (con⇓ (o , e , ar)) = 𝑎𝑙𝑔 (o , e , λ a → 𝕤𝕖𝕞 (AP→AM (Arity o) ar a))
--   𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v
--   𝕤𝕖𝕞 (mvar 𝔪 ε) = 𝑚𝑣𝑎𝑟 𝔪 (λ p → 𝕤𝕖𝕞 (index ε p))
--
--   𝕤𝕖𝕞ᵃ⇒ : M.MetaAlg⇒ CTmᵃ 𝒜ᵃ 𝕤𝕖𝕞
--   𝕤𝕖𝕞ᵃ⇒ = record
--     { ⟨𝑎𝑙𝑔⟩ = λ{ {t = o , e , ar} → cong (λ - → 𝑎𝑙𝑔 (o , -))
--                                     (cong (e ,_) (iext (dext λ a →
--                                       cong 𝕤𝕖𝕞 (M→P→M (Arity o) ar a)))) }
--     ; ⟨𝑣𝑎𝑟⟩ = refl
--     ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{ε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (λ v →
--                                   cong 𝕤𝕖𝕞 (ix∘tab≈id ε v))) } }
--
-- module CTm:⇓Theory {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) where
--   open M⇓.MetaAlg 𝒜ᵃ
--
--   𝕤𝕖𝕞 : CTm′ s ⇾̣ 𝒜
--   𝕤𝕖𝕞 (con⇓ (o , e , ar)) = 𝑎𝑙𝑔 (o , e , ArgProd₁ (Arity o) 𝕤𝕖𝕞 ar)
--   𝕤𝕖𝕞 (var x) = 𝑣𝑎𝑟 x
--   𝕤𝕖𝕞 (mvar 𝔪 ε) = 𝑚𝑣𝑎𝑟 𝔪 λ p → 𝕤𝕖𝕞 (index ε p)
--
--   𝕤𝕖𝕞⇓ᵃ⇒ : M⇓.MetaAlg⇒ CTm⇓ᵃ 𝒜ᵃ 𝕤𝕖𝕞
--   𝕤𝕖𝕞⇓ᵃ⇒ = record
--     { ⟨𝑎𝑙𝑔⟩ = refl
--     ; ⟨𝑣𝑎𝑟⟩ = refl
--     ; ⟨𝑚𝑣𝑎𝑟⟩ = (λ { {𝔪 = 𝔪} {ε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (λ p → cong 𝕤𝕖𝕞 (ix∘tab≈id ε p))) })
--     }
--
-- -- comp : 𝕋 ⇾̣ CTm
-- -- comp = 𝕋:Theory.𝕤𝕖𝕞 CTmᵃ
-- --
-- -- compᵃ⇒ : M.MetaAlg⇒ Tmᵃ CTmᵃ comp
-- -- compᵃ⇒ = 𝕋:Theory.𝕤𝕖𝕞ᵃ⇒ CTmᵃ
-- --
-- -- comp⇓ᵃ⇒ : M⇓.MetaAlg⇒ Tm⇓ᵃ CTm⇓ᵃ comp
-- -- comp⇓ᵃ⇒ = record { ⟨𝑎𝑙𝑔⟩ = cong con⇓ (trans (⅀F≅⅀⇓F.⇒.commute comp)
-- --                             (cong (⅀⇓₁ comp) (⅀F≅⅀⇓F.iso.isoʳ 𝕋)))
-- --                  ; ⟨𝑣𝑎𝑟⟩ = refl ; ⟨𝑚𝑣𝑎𝑟⟩ = refl }
-- --
-- -- 𝕤𝕖𝕞∘comp : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) (t : 𝕋 α Γ)
-- --         → CTm:⇓Theory.𝕤𝕖𝕞 𝒜ᵃ (comp t) ≡ 𝕋:Theory.𝕤𝕖𝕞 (M⇓→M 𝒜ᵃ) t
-- -- 𝕤𝕖𝕞∘comp 𝒜ᵃ t = 𝕋:⇓Theory.eq 𝒜ᵃ
-- --     (M⇓.MetaAlgProps.comp-hom _ _ (CTm:⇓Theory.𝕤𝕖𝕞⇓ᵃ⇒ 𝒜ᵃ) comp⇓ᵃ⇒)
-- --     (𝕋:⇓Theory.𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ) t
-- --
-- -- parse : CTm ⇾̣ 𝕋
-- -- parse = CTm:⇓Theory.𝕤𝕖𝕞 Tm⇓ᵃ
-- --
-- -- parse∘comp≈id : (t : 𝕋 α Γ) → parse (comp t) ≡ t
-- -- parse∘comp≈id t = trans (𝕤𝕖𝕞∘comp Tm⇓ᵃ t) (𝕋:⇓Theory.eq-id (𝕋:⇓Theory.𝕤𝕖𝕞ᵃ⇒ Tm⇓ᵃ) t)
--
-- -- open module rsd {𝒜} = ArgBuilder 𝒜 public
--
-- -- _$$_ : (o : O) → ArgMap (Arity o) 𝕋 Γ → 𝕋 (Sort o) Γ
-- -- _$$_ o ar = con (o , refl , ar)
--
--
-- -- module Constr (𝒜 : Familyₛ)(𝑎𝑙𝑔 : ⅀ 𝒜 ⇾̣ 𝒜) where
-- --   _$$_ : (o : O) → ArgMap (Arity o) 𝒜 Γ → 𝒜 (Sort o) Γ
-- --   _$$_ o ar = 𝑎𝑙𝑔 (o , refl , ar)
-- --
-- --   infix 1 _$$_
--
-- -- 𝕋:InitMetaAlg : InitialMetaAlg
-- -- 𝕋:InitMetaAlg = record { ⅀F = ⅀F ; ⅀:CompatStr = ⅀:CompatStr ; 𝕋:Init = 𝕋:Init }
-- --
-- -- module 𝕋:Theory = InitialMetaAlg.Theory 𝕋:InitMetaAlg
--
-- {-}
-- module _ {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) where
--   open M⇓.MetaAlg 𝒜ᵃ
--
--   sem⇓′ : CTm′ s ⇾̣ 𝒜
--   sem⇓′ (con⇓ (o , e , ar)) = 𝑎𝑙𝑔 (o , e , ArgProd₁ (Arity o) sem⇓′ ar)
--   sem⇓′ (var x) = 𝑣𝑎𝑟 x
--   sem⇓′ (mvar 𝔪 ε) = 𝑚𝑣𝑎𝑟 𝔪 λ p → sem⇓′ (index ε p)
--
--   sem⇓′ᵃ⇒ : M⇓.MetaAlg⇒ CTm⇓ᵃ 𝒜ᵃ sem⇓′
--   sem⇓′ᵃ⇒ = record
--     { ⟨𝑎𝑙𝑔⟩ = refl
--     ; ⟨𝑣𝑎𝑟⟩ = refl
--     ; ⟨𝑚𝑣𝑎𝑟⟩ = (λ { {𝔪 = 𝔪} {ε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (λ p → cong sem⇓′ (ix∘tab≈id ε p))) })
--     }
--
-- comp : 𝕋 ⇾̣ CTm
-- comp = 𝕋:Theory.𝕤𝕖𝕞 CTmᵃ
--
-- compᵃ⇒ : M.MetaAlg⇒ Tmᵃ CTmᵃ comp
-- compᵃ⇒ = 𝕋:Theory.ᵃ⇒ CTmᵃ
--
-- comp⇓ᵃ⇒ : M⇓.MetaAlg⇒ Tm⇓ᵃ CTm⇓ᵃ comp
-- comp⇓ᵃ⇒ = record { ⟨𝑎𝑙𝑔⟩ = λ{ {t = o , e , ar} → cong (λ - → con⇓ (o , -))
--   (cong (e ,_) (trans ((AM→AP-commute (Arity o) comp (AP→AM (Arity o) ar)))
--                 (cong (ArgProd₁ (Arity o) comp) (P→M→P (Arity o) ar)))) }
--   ; ⟨𝑣𝑎𝑟⟩ = refl ; ⟨𝑚𝑣𝑎𝑟⟩ = refl }
--
-- parse : CTm ⇾̣ 𝕋
-- parse = sem⇓′ Tm⇓ᵃ
--
-- foo : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → 𝕋 ⇾̣ 𝒜
-- foo 𝒜ᵃ t = sem⇓′ 𝒜ᵃ (comp t)
--
-- fooᵃ⇒ : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → M⇓.MetaAlg⇒ Tm⇓ᵃ 𝒜ᵃ (foo 𝒜ᵃ) -- M⇓.MetaAlg⇒ Tm⇓ᵃ 𝒜ᵃ foo
-- fooᵃ⇒ 𝒜ᵃ = CategoryProps.comp-hom M⇓.MetaAlgebraCatProps (sem⇓′ 𝒜ᵃ) comp (sem⇓′ᵃ⇒ 𝒜ᵃ) comp⇓ᵃ⇒
--
-- bar : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → 𝕋 ⇾̣ 𝒜
-- bar {𝒜} 𝒜ᵃ t = 𝕋:Theory.𝕤𝕖𝕞 (M⇓→M 𝒜ᵃ) t
--
-- barᵃ⇒ : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → M⇓.MetaAlg⇒ Tm⇓ᵃ 𝒜ᵃ (bar 𝒜ᵃ) -- M⇓.MetaAlg⇒ Tm⇓ᵃ 𝒜ᵃ foo
-- barᵃ⇒ 𝒜ᵃ = 𝕋:⇓Theory.ᵃ⇒ 𝒜ᵃ
--
-- foo=bar : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → (t : 𝕋 α Γ) → sem⇓′ 𝒜ᵃ (comp t) ≡ 𝕋:Theory.𝕤𝕖𝕞 (M⇓→M 𝒜ᵃ) t
-- foo=bar 𝒜ᵃ = 𝕋:⇓Theory.eq 𝒜ᵃ (fooᵃ⇒ 𝒜ᵃ) (barᵃ⇒ 𝒜ᵃ)
--
-- -- bar : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → 𝕋 ⇾̣ 𝒜
-- -- bar {𝒜} 𝒜ᵃ t = Semantics.𝕤𝕖𝕞 (qux 𝒜ᵃ) t
-- --   where open M⇓.MetaAlg 𝒜ᵃ
--
--
-- parse∘comp≈id : (t : 𝕋 α Γ) → parse (comp t) ≡ t
-- parse∘comp≈id t = trans (foo=bar Tm⇓ᵃ t) (𝕋:⇓Theory.eq-id (barᵃ⇒ Tm⇓ᵃ) t)
-- -- parse∘comp≈id = 𝕋:Theory.eq-id (CategoryProps.comp-hom M.MetaAlgebraCatProps
-- --                           parse comp (sem⇓ᵃ⇒ Tmᵃ) (𝕋:Theory.ᵃ⇒ CTmᵃ))
--
--
-- --
-- -- comp : 𝕋 ⇾̣ CTm
-- -- comp = Semantics.𝕤𝕖𝕞 CTmᵃ
-- --
-- -- blah : M⇓.MetaAlg 𝕋
-- -- blah = record
-- --   { 𝑎𝑙𝑔 = λ{ (o , e , ar) → con (o , (e , (λ x → AP→AM (Arity o) ar x))) }
-- --   ; 𝑣𝑎𝑟 = var
-- --   ; 𝑚𝑣𝑎𝑟 = λ z → mvar z
-- --   }
-- --
-- -- module _ {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) where
-- --   open M⇓.MetaAlg 𝒜ᵃ
-- --   nedne : 𝕋 ⇾̣ 𝒜
-- --   nedne (con (o , e , ar)) = 𝑎𝑙𝑔 (o , (e , (AM→AP (Arity o) (λ z → nedne (ar z)))))
-- --   nedne (var x) = 𝑣𝑎𝑟 x
-- --   nedne (mvar x x₁) = 𝑚𝑣𝑎𝑟 x (λ z → nedne (x₁ z))
-- --
-- --   serm⇓ : CTm′ s ⇾̣ 𝒜
-- --   serm⇓ (con⇓ (o , e , ar)) = 𝑎𝑙𝑔 (o , (e , (ArgProd₁ (Arity o) serm⇓ ar)))
-- --   serm⇓ (var x) = 𝑣𝑎𝑟 x
-- --   serm⇓ (mvar x x₁) = 𝑚𝑣𝑎𝑟 x λ x₂ → serm⇓ (index x₁ x₂)
-- --
-- -- module _ {𝒜 : Familyₛ} (𝒜ᵃ : MetaAlg 𝒜) where
-- --   open MetaAlg 𝒜ᵃ
-- --   sem⇓ : CTm′ s ⇾̣ 𝒜
-- --   sem⇓ (con⇓ (o , e , ar)) = 𝑎𝑙𝑔 (o , (e , (λ a → sem⇓ (AP→AM (Arity o) ar a))))
-- --   sem⇓ (var v) = 𝑣𝑎𝑟 v
-- --   sem⇓ (mvar 𝔪 ε) = 𝑚𝑣𝑎𝑟 𝔪 (λ p → sem⇓ (index ε p))
-- --
-- --   sem⇓ᵃ⇒ : M.MetaAlg⇒ CTmᵃ 𝒜ᵃ sem⇓
-- --   sem⇓ᵃ⇒ = record
-- --     { ⟨𝑎𝑙𝑔⟩ = λ{ {t = o , e , ar} → cong (λ - → 𝑎𝑙𝑔 (o , -))
-- --                                     (cong (e ,_) (iext (dext λ a →
-- --                                       cong sem⇓ (M→P→M (Arity o) ar a)))) }
-- --     ; ⟨𝑣𝑎𝑟⟩ = refl
-- --     ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{ε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (λ v →
-- --                                   cong sem⇓ (ix∘tab≈id ε v))) } }
-- --
-- -- parse : CTm ⇾̣ 𝕋
-- -- parse = sem⇓ Tmᵃ
-- --
-- -- foo : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → 𝕋 ⇾̣ 𝒜
-- -- foo 𝒜ᵃ t = serm⇓ 𝒜ᵃ (comp t)
-- --
-- -- -- fooᵃ : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → MA.MetaAlg⇒ ⅀⇓F 𝔛 blah 𝒜ᵃ (foo 𝒜ᵃ)
-- -- -- fooᵃ 𝒜ᵃ  = record
-- -- --   { ⟨𝑎𝑙𝑔⟩ = λ{ {t = o , e , ar} → {! cong (λ - → MA.Semantics.𝑎𝑙𝑔 ⅀⇓F 𝔛 𝒜ᵃ (o , e , -))  !} }
-- -- --   ; ⟨𝑣𝑎𝑟⟩ = refl
-- -- --   ; ⟨𝑚𝑣𝑎𝑟⟩ = {!   !} }
-- --
-- -- qux : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → MetaAlg 𝒜
-- -- qux {𝒜} 𝒜ᵃ = record { 𝑎𝑙𝑔 = λ x → 𝑎𝑙𝑔 (⅀F≅⅀⇓F.⇒.η 𝒜 x) ; 𝑣𝑎𝑟 = 𝑣𝑎𝑟 ; 𝑚𝑣𝑎𝑟 = 𝑚𝑣𝑎𝑟 }
-- --   where open M⇓.MetaAlg 𝒜ᵃ
-- --
-- -- bar : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → 𝕋 ⇾̣ 𝒜
-- -- bar {𝒜} 𝒜ᵃ t = Semantics.𝕤𝕖𝕞 (qux 𝒜ᵃ) t
-- --   where open M⇓.MetaAlg 𝒜ᵃ
-- -- sub⇓ : CTm ⇾̣ 〖 CTm , CTm 〗
-- -- sub⇓ t σ = comp (𝕤𝕦𝕓 (parse t) (parse ∘ σ))
-- --
-- -- [_/]⇓ : CTm α Γ → CTm β (α ∙ Γ) → CTm β Γ
-- -- [ t /]⇓ s = comp ([ (parse t) /] (parse s))
-- --
-- open ArgBuilder 𝕋 public
--
-- _$$_ : (o : O) → ArgMap (Arity o) 𝕋 Γ → 𝕋 (Sort o) Γ
-- _$$_ o ar = con (o , refl , ar)
--
-- infix 1 _$$_
--
-- -- comp∘parse≈id : (t : CTm α Γ) → comp (parse t) ≡ t
-- -- comp∘parse≈id (con⇓ (o , e , ar)) = cong (λ - → con⇓ (o , e , -))-- {!   !}
-- --   (begin
-- --       AM→AP (Arity o) (λ a → comp (parse (AP→AM (Arity o) ar a)))
-- --   ≡⟨ AM→AP-commute (Arity o) (comp ∘ parse) (λ a → (AP→AM (Arity o) ar a)) ⟩
-- --       ArgProd₁ (Arity o) (comp ∘ parse) (AM→AP (Arity o) (AP→AM (Arity o) ar))
-- --   ≡⟨ cong (ArgProd₁ (Arity o) (comp ∘ parse)) (P→M→P (Arity o) ar) ⟩
-- --       ArgProd₁ (Arity o) (λ t → comp (parse t)) ar
-- --   ≡⟨ Functor.F-resp-≈ (ArgProdF (Arity o)) (λ{ {x = t} → comp∘parse≈id t }) ⟩ --cong (λ{ - → ArgProd₁ (Arity o) (λ {τ} → - {τ = τ}) ar}) (ext λ t → ?) ⟩
-- --       ArgProd₁ (Arity o) id ar
-- --   ≡⟨ {!   !} ⟩
-- --       ar
-- --   ∎) where open ≡-Reasoning
-- -- -- AM→AP (Arity o) (λ a → comp (parse (AP→AM (Arity o) ar a)))
-- -- -- ≡ con⇓ (o , e , ar)
-- -- comp∘parse≈id (var x) = refl
-- -- comp∘parse≈id (mvar 𝔪 ε) = cong (mvar 𝔪) {!   !}
-- -- tabulate (λ p → comp (parse (index ε p))) ≡ ε
--
--
-- -- nedhne : {𝒜 : Familyₛ}(𝒜ᵃ : M⇓.MetaAlg 𝒜) → (t : 𝕋 α Γ) → foo 𝒜ᵃ t ≡ bar 𝒜ᵃ t
-- -- nedhne 𝒜ᵃ t = Trav.Semantics.eq ⅀⇓F {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !}
-- -}
-- {-}
-- Hi Marcelo,
--
-- I played around with the things you suggested above:
--
-- – The comp t = comp s  -->  t = s proof indeed goes through easily by the one-sided inverse property.
--
-- – The size-indexed version of the other inverse property
--
-- 	(i :  Size) (t : CTm′ i α Γ) → comp (parse i t) ≡ φ ∞ i t
--
-- doesn’t work unfortunately: the inductive call is accepted, but there is a step that needs something similar to the muφ postulate, specifically the step
--
-- 	con⇓ ∞ (o , e , AM→AP (Arity o) (λ a → φ ∞ k (AP→AM (Arity o) ar a)))
--  ≡⟨  ⟩
-- 	con⇓ k (o , e , AM→AP (Arity o) (AP→AM (Arity o) ar))
--
-- – The lemma  parse i ( φ i j t )  ≡ parse j t  can be proved fine with patter-match and refl,  but I can't see how to prove the injectivity of parse (with the lemma or otherwise). Did you have a particular approach in mind?
--
-- CTm : Familyₛ parse i ( φ i j t )
-- CTm = CTm′ ∞
--
-- CTmᵃ : MetaAlg CTm
-- CTmᵃ = record
--   { 𝑎𝑙𝑔 = λ{ (o , e , ar) → con⇓ (o , e , AM→AP (Arity o) ar) }
--   ; 𝑣𝑎𝑟 = var
--   ; 𝑚𝑣𝑎𝑟 = λ 𝔪 ε → mvar 𝔪 (tabulate ε) }
--
-- comp : 𝕋 ⇾̣ CTm
-- comp = Semantics.𝕤𝕖𝕞 CTmᵃ
--
-- module _ {𝒜 : Familyₛ} (𝒜ᵃ : MetaAlg 𝒜) where
--   open MetaAlg 𝒜ᵃ
--   sem⇓ : CTm′ s ⇾̣ 𝒜
--   sem⇓ (con⇓ (o , e , ar)) = 𝑎𝑙𝑔 (o , (e , (λ a → sem⇓ (AP→AM (Arity o) ar a))))
--   sem⇓ (var v) = 𝑣𝑎𝑟 v
--   sem⇓ (mvar 𝔪 ε) = 𝑚𝑣𝑎𝑟 𝔪 (λ p → sem⇓ (index ε p))
--
--   sem⇓ᵃ⇒ : MetaAlg⇒ CTmᵃ 𝒜ᵃ sem⇓
--   sem⇓ᵃ⇒ = record
--     { ⟨𝑎𝑙𝑔⟩ = λ{ {t = o , e , ar} → cong (λ - → 𝑎𝑙𝑔 (o , -))
--                                     (cong (e ,_) (iext (dext λ a →
--                                       cong sem⇓ (M→P→M (Arity o) ar a)))) }
--     ; ⟨𝑣𝑎𝑟⟩ = refl
--     ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{ε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (λ v →
--                                   cong sem⇓ (ix∘tab≈id ε v))) } }
--
--
-- parse : CTm ⇾̣ 𝕋
-- parse = sem⇓ Tmᵃ
--
-- parse∘comp≈id : (t : 𝕋 α Γ) → parse (comp t) ≡ t
-- parse∘comp≈id = eq-id (CategoryProps.comp-hom MetaAlgebraCatProps
--                           parse comp (sem⇓ᵃ⇒ Tmᵃ) (Semantics.ᵃ⇒ CTmᵃ))
--
-- comp-inj : (t s : 𝕋 α Γ) → comp t ≡ comp s → t ≡ s
-- comp-inj t s p = begin t               ≡˘⟨ parse∘comp≈id t ⟩
--                        parse (comp t)  ≡⟨ cong parse p ⟩
--                        parse (comp s)  ≡⟨ parse∘comp≈id s ⟩
--                        s               ∎ where open ≡-Reasoning
--
-- -- comp∘parse≈id : (t : CTm α Γ) → comp (parse t) ≡ t
-- -- comp∘parse≈id (con⇓ (o , e , ar)) = cong (λ - → con⇓ (o , e , -)) {!   !}
-- -- -- AM→AP (Arity o) (λ a → comp (parse (AP→AM (Arity o) ar a)))
-- -- -- ≡ con⇓ (o , e , ar)
-- -- comp∘parse≈id (var x) = refl
-- -- comp∘parse≈id (mvar 𝔪 ε) = cong (mvar 𝔪) {!   !}
-- -- -- tabulate (λ p → comp (parse (index ε p))) ≡ ε
--
-- -}
