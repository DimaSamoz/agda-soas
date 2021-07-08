
open import SOAS.Common

-- Free construction with respect to a forgetful functor between categories
module SOAS.Construction.Free {ℂ 𝕊 : Category 1ℓ 0ℓ 0ℓ}
                               (U : Functor 𝕊 ℂ) where

open import Categories.Adjoint
import Categories.Morphism.Reasoning as MR
open import Categories.Category.Equivalence using (WeakInverse; StrongEquivalence)
open import Categories.Adjoint.Properties
open import Categories.Monad


private module ℂ = Category ℂ
private module 𝕊 = Category 𝕊
private module U = Functor U

-- Mapping from an object of the carrier category to the carrier of an object
-- from the structure category
_↪_ : ℂ.Obj → 𝕊.Obj → Set
C ↪ S = ℂ [ C , U.₀ S ]


-- Definition of F being a free structure over a carrier C:
-- any carrier map c : C → S into the carrier of a structure S factorises
-- through a unique extension of c to a structure homomorphism ĉ : F C → S:
--
--           ⌊-⌋
--   C ────────────── FC
--  ╰─────── S ───────╯
--      c         ĉ

record FreeConstruction (F : ℂ.Obj → 𝕊.Obj)
                        (C : ℂ.Obj)
                        (embed : C ↪ F C)
                        (S : 𝕊.Obj)
                        (c : C ↪ S)
                        : Set₁ where

  field
    -- Given another structure S, any mapping from C to the carrier of S can be
    -- extended into a structure homomorphism from F C to S.
    extend : 𝕊 [ F C , S ]

    -- Any map from C to the carrier of a structure S factors through the
    -- embedding and extension
    factor : U.₁ extend ℂ.∘ embed ℂ.≈ c

    -- Extension is the unique factorising morphism
    unique : (e : 𝕊 [ F C , S ])
           → (p : (U.₁ e ℂ.∘ embed) ℂ.≈ c)
           → 𝕊 [ e ≈ extend ]

record FreeMapping (F : ℂ.Obj → 𝕊.Obj) : Set₁ where

  field
    embed : {C : ℂ.Obj} → C ↪ F C
    univ  : (C : ℂ.Obj) (S : 𝕊.Obj)(c : C ↪ S)
          → FreeConstruction F C embed S c

  module Universal C S c = FreeConstruction (univ C S c)

  module _ {C : ℂ.Obj} {S : 𝕊.Obj}(c : C ↪ S) where
    open Universal C S c public

  open MR ℂ
  open ℂ.HomReasoning
  private module 𝕊R = 𝕊.HomReasoning
  open NT

  -- The uniqueness of the factors means that any two morphisms
  -- that factorise the same arrow must be equal
  equate : {C : ℂ.Obj}{S : 𝕊.Obj}
        → (f g : 𝕊 [ F C , S ])
        → (p : U.₁ f ℂ.∘ embed ℂ.≈ U.₁ g ℂ.∘ embed)
        → 𝕊 [ f ≈ g ]
  equate f g p = unique _ f p 𝕊R.○ 𝕊R.⟺ (unique _ g ℂ.Equiv.refl)

  -- Infix shorthand
  [_≋_]! : {C : ℂ.Obj}{S : 𝕊.Obj}
        → (f g : 𝕊 [ F C , S ])
        → (p : U.₁ f ℂ.∘ embed ℂ.≈ U.₁ g ℂ.∘ embed)
        → 𝕊 [ f ≈ g ]
  [ f ≋ g ]! p = equate f g p

  -- Extensions of equal embeddings are equal
  extend-cong : {C : ℂ.Obj}{S : 𝕊.Obj}(c₁ c₂ : C ↪ S)
             → ℂ [ c₁ ≈ c₂ ] → 𝕊 [ extend c₁ ≈ extend c₂ ]
  extend-cong {C}{S} c₁ c₂ p = unique _ (extend c₁) (factor c₁ ○ p)


  -- | Freeness makes F into a functor

  map : {C D : ℂ.Obj} → C ℂ.⇒ D → F C 𝕊.⇒ F D
  map {C}{D} f = extend (embed ℂ.∘ f)

  embed-commute : {C D : ℂ.Obj}(f : C ℂ.⇒ D)
               → embed ℂ.∘ f ℂ.≈ (U.₁ (map f) ℂ.∘ embed)
  embed-commute {C}{D} f = ⟺ (factor (embed ℂ.∘ f))

  identity : {C : ℂ.Obj} → map (ℂ.id {C}) 𝕊.≈ 𝕊.id
  identity {C} = 𝕊R.⟺ $ᶠ unique _ 𝕊.id (begin
         U.₁ 𝕊.id ℂ.∘ embed  ≈⟨ U.identity ⟩∘⟨refl ⟩
         ℂ.id ℂ.∘ embed      ≈⟨ id-comm-sym ⟩
         embed ℂ.∘ ℂ.id      ∎)

  homomorphism : {C D E : ℂ.Obj} {f : ℂ [ C , D ]} {g : ℂ [ D , E ]}
              → 𝕊 [ map (ℂ [ g ∘ f ])
               ≈ 𝕊 [ map g ∘ map f ] ]
  homomorphism {C}{D}{E}{f}{g} = 𝕊R.⟺ $ᶠ unique _ (𝕊 [ map g ∘ map f ]) (begin
         U.₁ (map g 𝕊.∘ map f) ℂ.∘ embed           ≈⟨ pushˡ U.homomorphism ⟩
         U.₁ (map g)  ℂ.∘  U.₁ (map f)  ℂ.∘ embed  ≈⟨ pushʳ (⟺ (embed-commute f)) ⟩
         (U.₁ (map g)  ℂ.∘  embed) ℂ.∘ f           ≈⟨ pushˡ (⟺ (embed-commute g)) ⟩
         embed ℂ.∘ g ℂ.∘ f                          ∎)

  -- Free functor from ℂ to 𝕊
  Free : Functor ℂ 𝕊
  Free = record
    { F₀ = F
    ; F₁ = map
    ; identity = identity
    ; homomorphism = homomorphism
    ; F-resp-≈ = λ {C}{D}{f}{g} p →
          extend-cong (embed ℂ.∘ f) (embed ℂ.∘ g) (ℂ.∘-resp-≈ʳ p)
    }

  module F = Functor Free

  -- | Freeness also induces a free-forgetful adjunction

  -- Embedding is a natural transformation
  embed-NT : NT idF (U ∘F Free)
  embed-NT = ntHelper record
    { η = λ C → embed
    ; commute = embed-commute
    }

  -- Extension of the identity on US is a natural transformation
  extract : (S : 𝕊.Obj) → F (U.₀ S) 𝕊.⇒ S
  extract S = extend ℂ.id

  -- Extraction is a natural transformation
  extract-NT : NT (Free ∘F U) idF
  extract-NT = ntHelper record
    { η = extract
    ; commute = λ {S}{T} f → [ extract T 𝕊.∘ F.₁ (U.₁ f) ≋ f 𝕊.∘ extract S ]!
        (begin
             U.₁ (extract T 𝕊.∘ F.₁ (U.₁ f)) ℂ.∘ embed
        ≈⟨ pushˡ U.homomorphism ⟩
             U.₁ (extract T) ℂ.∘ U.₁ (F.₁ (U.₁ f)) ℂ.∘ embed
        ≈⟨ refl⟩∘⟨ sym-commute embed-NT (U.₁ f) ⟩
             U.₁ (extract T) ℂ.∘ embed ℂ.∘ U.₁ f
        ≈⟨ pullˡ (factor ℂ.id) ○ ℂ.identityˡ ⟩
             U.₁ f
        ≈˘⟨ (refl⟩∘⟨ factor ℂ.id) ○ ℂ.identityʳ ⟩
             U.₁ f ℂ.∘ U.₁ (extract S) ℂ.∘ embed
        ≈˘⟨ pushˡ U.homomorphism ⟩
             U.₁ (f 𝕊.∘ extract S) ℂ.∘ embed
        ∎)
    }

  -- The free-forgetful adjunction arising from the universal morphisms
  Free⊣Forgetful : Free ⊣ U
  Free⊣Forgetful = record
    { unit = embed-NT
    ; counit = extract-NT
    ; zig = λ {C} → [ extract (F.₀ C) 𝕊.∘ F.₁ embed ≋ 𝕊.id ]!
        (begin
             U.₁ (extract (F.₀ C) 𝕊.∘ F.₁ embed) ℂ.∘ embed
         ≈⟨ pushˡ U.homomorphism ⟩
             U.₁ (extract (F.₀ C)) ℂ.∘ U.₁ (F.₁ embed) ℂ.∘ embed
         ≈⟨ refl⟩∘⟨ (sym-commute embed-NT embed) ⟩
             U.₁ (extract (F.₀ C)) ℂ.∘ (embed ℂ.∘ embed)
         ≈⟨ pullˡ (factor (ℂ.id)) ⟩
             ℂ.id ℂ.∘ embed
         ≈˘⟨ U.identity ⟩∘⟨refl ⟩
             U.₁ 𝕊.id ℂ.∘ embed
         ∎)
    ; zag = factor ℂ.id
    }

  FreeMonad : Monad ℂ
  FreeMonad = adjoint⇒monad Free⊣Forgetful
