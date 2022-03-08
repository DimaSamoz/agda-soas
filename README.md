# SOAS: Second-Order Abstract Syntax
An Agda formalisation framework for second-order languages.

Accompanies the POPL 2022 paper [Formal Metatheory of Second-Order Abstract Syntax](https://www.cl.cam.ac.uk/~ds709/agda-soas/).

### Quick start

Run
```
python soas.py <syntax> [-o <output>]
```
with `<syntax>` as a path to a syntax file (examples given in `gen/ex`, e.g. `python soas.py gen/ex/lambda/stlc`). This assumes `python` is Python 3. By default the generated Agda modules will be saved in the `out` directory, but this can be customised with the `-o` argument.

* [Introduction](#introduction)
* [Usage](#usage)
  + [Syntax description language](#syntax-description-language)
  + [Agda formalisation](#agda-formalisation)
    - [`Signature.agda`](#-signatureagda-)
    - [`Syntax.agda`](#-syntaxagda-)
    - [`Equality.agda`](#-equalityagda-)
    - [Equational reasoning](#equational-reasoning)
  + [Additional features](#additional-features)
    - [Derived constructions](#derived-constructions)
    - [Algebraic properties](#algebraic-properties)
    - [Module system](#module-system)


## Introduction

SOAS is a library for generating the formalised metatheory of second-order syntaxes, i.e. languages that involve terms with variable binding. Examples are the abstraction terms of computational calculi like the λ-calculus, quantifiers of first-order logic, differentiation and integration operators, etc. Formalising such systems in a proof assistant usually involves a lot of boilerplate, generally associated with the representation of variable binding and capture-avoiding substitution, the latter of which plays a role in the equational theory or computational behaviour of second-order languages (e.g. instantiation or β-reduction).

Starting from the description of the second-order signature and equational presentation of a syntax, such as the following one for the simply typed λ-calculus:

```txt
syntax STLC | Λ

type
  N   : 0-ary
  _↣_ : 2-ary | r30

term
  app  : α ↣ β   α  ->  β       | _$_ l20
  lam  : α.β        ->  α ↣ β   | ƛ_  r10

theory
  (ƛβ) b : α.β  a : α |> app (lam(x.b[x]), a) = b[a]
  (ƛη) f : α ↣ β      |> lam (x. app(f, x))   = f
```

the library generates Agda code for:

* a grammar of types and an intrinsically-typed data type of terms;
* operations of weakening and substitution together with their correctness properties;
* a record that, when instantiated with a mathematical model, induces a semantic interpretation of the syntax in the model that preserves substitution;
* a term constructor for parametrised metavariables and the operation of metasubstitution;
* and a library for second-order equational/rewriting reasoning based on the axioms.

## Directory structure

The high-level directory structure of the project is shown below:
```
.
├── Everything.agda   | All the Agda modules that make up the library
├── SOAS              | Main source directory
├── gen               | Code generation script directory
│   ├── ex            | Example syntax files
│   ├── templates     | Template files used in generation
│   ├── term.py       | Term parsing and output
│   ├── type.py       | Type parsing and output
│   ├── eq.py         | Equality parsing and output
│   └── util.py       | Utilities
├── out               | Agda modules generated from the examples
└── soas.py           | Main entry script for the code generator
```

A browsable version of the library source code can be found [here](https://www.cl.cam.ac.uk/~ds709/agda-soas/code/Everything.html), and the example generated Agda modules [here](https://www.cl.cam.ac.uk/~ds709/agda-soas/ex/Examples.html).

## Usage

### Syntax description language

The SOAS framework includes a Python script `soas.py` that compiles a simple and flexible syntax description language into Agda code. The language includes several features to make the construction of first- and second-order syntaxes as seamless as possible, such as (meta)syntactic shorthands, a module system, and a library of common algebraic properties. We start with the description of a basic syntax file for the simply-typed λ-calculus, and introduce various extensions [below](#additional-features).

A syntax description file consists of four components: the syntax header, the type declaration, the term operators, and the equational theory. The latter three are given under indented blocks preceded by the keywords `type`, `term` and `theory`. Lines beginning with `--` are parsed as comments and are therefore ignored.
```
syntax STLC | Λ
```
`STLC` is the root name of the generated Agda modules `STLC.Signature`, `STLC.Syntax`, `STLC.Equality`. This would be used as the name of the data type of terms and type signature, but we override it with the optional annotation `… | Λ` so the Agda type of terms is `Λ` and Agda type of sorts/types is `ΛT`.
```
type
  N   : 0-ary
  _↣_ : 2-ary | r30
```
Types must be given in an indented list of operators and arities, with optional attributes. We specify a nullary type constructor `N`, and a binary type constructor `_↣_`. The annotation `… | r30` declares the associativity and precedence of the binary infix operator, and gets turned into the Agda fixity declaration `infixr 30 _↣_`.
```
term
  app  : α ↣ β   α  ->  β       | _$_ l20
  lam  : α.β        ->  α ↣ β   | ƛ_  r10
```
Terms are given by a list of textual operator names and their type declarations, with optional annotations for symbolic notation and fixity. The type of an operator consists of a return sort given after a `->`, and a sequence of argument sorts separated by at least two spaces. The arguments may optionally bind any number of variables, written as `(α₁,…,αₖ).β` or just `α.β` if there is only one bound variable (like in the case of `lam` above). The textual operator names are used in the equational theory, for the operator symbols for the Agda term signature, and the constructors of the inductive family of terms. The latter may be overridden to a different symbol (that can be Unicode and mixfix, with a given fixity) with an annotation like `… | _$_ l20` or `… | ƛ_  r10`.

```
theory
  (ƛβ) b : α.β  a : α |> app (lam(x.b[x]), a) = b[a]
  (ƛη) f : α ↣ β      |> lam (x. app(f, x))   = f
```
The equational axioms of a syntax are given as a list of pairs of terms in
metavariable and object variable contexts. The general form of an axiom is `(AN)
𝔐 |> Γ |- s = t`, where `AN` is the name of the axiom, <code>𝔐 = m₁ : Π₁.τ₁
&nbsp;…&nbsp; mₖ : Πₖ.τₖ</code> is a double space–separated list of parametrised
metavariables, <code>Γ = x₁ : α₁  &nbsp;…&nbsp;  xₗ : αₗ</code> is a double
space–separated list of object variables, and `s` and `t` are terms consisting
of metavariables, object variables, and operator applications. If
`Γ` is empty (as it often will be), the `… Γ |- …` part of the declaration can
be omitted; similarly, (meta)variables of the same sort can be grouped as `a b c
: τ`, and if `: τ` is not given, the variable type will default to the sort `*`,
denoting un(i)sortedness. The operator applications in the terms are of the form
`op (t₁, …, tₘ)`, where the arguments may bind variables using `.`: for example, a binary
operator `op` that binds two variables in the first argument and none in the
second is written as `op (a b.t[a,b], s)`. The terms associated with a metavariable environment are given between square brackets which may be omitted if the metavariable has no parameters. Given all this, the axiom `ƛβ` is read as: given an arbitrary term `b` of type `β` with a free variable of type `α`, and a term `a` of type `α`, the application of the abstraction `lam(x.b[x])` to `a` is equal to `b` with all occurrences of the free variable replaced by `a`. Every application of β-equivalence is an instance of this axiom, with `b` and `a` instantiated with concrete terms of the right type and context.

### Agda formalisation

The script generates three Agda files (two if an equational theory is not given).

#### `Signature.agda`

The signature file contains:

* the (first-order) type declaration for the syntax, if it exists:
  ```agda
  data ΛT : Set where
    N   : ΛT
    _↣_ : ΛT → ΛT → ΛT
  infixr 30 _↣_
  ```
* the list of operator symbols parametrised by type variables:
  ```agda
  data Λₒ : Set where
    appₒ : {α β : ΛT} → Λₒ
    lamₒ : {α β : ΛT} → Λₒ
  ```

* the term signature that maps operator symbols to arities:

  ```agda
  Λ:Sig : Signature Λₒ
  Λ:Sig = sig λ
    { (appₒ {α}{β}) → (⊢₀ α ↣ β) , (⊢₀ α) ⟼₂ β
    ; (lamₒ {α}{β}) → (α ⊢₁ β)            ⟼₁ α ↣ β
    }
  ```
  An arity consists of a list of second-order arguments and a return type. An argument may bind any number of variables. For example, the application operator has two arguments of sort `α ↣ β` and `α`, binding no variables and returning a `β`. The lambda abstraction operator has one argument of sort `β` that binds a variable of sort `α`, and returns a function term of sort `α ↣ β`. This second-order binding signature is sufficient to fully specify the syntactic structure of the calculus.

#### `Syntax.agda`

The syntax file contains:

* the intrinsically-typed inductive family of terms with variables, metavariables (from a family `𝔛`) and symbolic operators:
  ```agda
  data Λ : Familyₛ where
    var  : ℐ ⇾̣ Λ
    mvar : 𝔛 α Π → Sub Λ Π Γ → Λ α Γ

    _$_ : Λ (α ↣ β) Γ → Λ α Γ → Λ β Γ
    ƛ_  : Λ β (α ∙ Γ) → Λ (α ↣ β) Γ

  infixl 20 _$_
  infixr 10 ƛ_
  ```
* an instance of the algebra of the signature endofunctor, mapping operator symbols to terms of the syntax:
  ```agda
  Λᵃ : SynAlg Λ
  Λᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (appₒ ⅋ a , b) → _$_ a b
      (lamₒ ⅋ a)     → ƛ_  a
    ; 𝑣𝑎𝑟 = var
    ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }
  ```
* semantic interpretation of terms in any signature algebra `(𝒜, 𝑣𝑎𝑟, 𝑚𝑣𝑎𝑟, 𝑎𝑙𝑔)`:
  ```agda
  𝕤𝕖𝕞 : Λ ⇾̣ 𝒜
  𝕊 : Sub Λ Π Γ → Π ~[ 𝒜 ]↝ Γ
  𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
  𝕊 (t ◂ σ) (old v) = 𝕊 σ v
  𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
  𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

  𝕤𝕖𝕞 (_$_ a b) = 𝑎𝑙𝑔 (appₒ ⅋ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
  𝕤𝕖𝕞 (ƛ_  a)   = 𝑎𝑙𝑔 (lamₒ ⅋ 𝕤𝕖𝕞 a)
  ```

* proof that the interpretation is a signature algebra homomorphism:
  ```agda
  𝕤𝕖𝕞ᵃ⇒ : SynAlg⇒ Λᵃ 𝒜ᵃ 𝕤𝕖𝕞
  𝕤𝕖𝕞ᵃ⇒ = record
    { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
    ; ⟨𝑣𝑎𝑟⟩ = refl
    ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
    where
    open ≡-Reasoning
    ⟨𝑎𝑙𝑔⟩ : (t : ⅀ Λ α Γ) → 𝕤𝕖𝕞 (Λᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
    ⟨𝑎𝑙𝑔⟩ (appₒ ⅋ _) = refl
    ⟨𝑎𝑙𝑔⟩ (lamₒ ⅋ _) = refl

    𝕊-tab : (mε : Π ~[ Λ ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
    𝕊-tab mε new     = refl
    𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v
  ```

* proof that the interpretation is unique, i.e. it is equal to any signature algebra–homomorphism `g`:
  ```agda
  𝕤𝕖𝕞! : (t : Λ α Γ) → 𝕤𝕖𝕞 t ≡ g t
  𝕊-ix : (mε : Sub Λ Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
  𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
  𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
  𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
    = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
  𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

  𝕤𝕖𝕞! (_$_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
  𝕤𝕖𝕞! (ƛ_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
  ```
* instantiation of the generic second-order metatheory with the syntax. The `Theory` module contains operations such as variable renaming `𝕣𝕖𝕟`, variable substitution `𝕤𝕦𝕓`, and special cases such as weakening `𝕨𝕜 : Λ α Γ → Λ α (τ ∙ Γ)` and single-variable substitution `[_/]_ : Λ β Γ → Λ α (β ∙ Γ) → Λ α Γ`. It also contains various correctness properties of the operations, such as the syntactic and semantic substitution lemmas. See [here](out/STLC/Model.agda) for an example of how these can be used.

#### `Equality.agda`

The equational theory file contains the axiom declaration of the syntax, and the instantiation of the generic second-order equational reasoning library.
```agda
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ Λ) α Γ → (𝔐 ▷ Λ) α Γ → Set where
  ƛβ : ⁅ α ⊩ β ⁆ ⁅ α ⁆̣ ▹ ∅ ⊢ (ƛ 𝔞⟨ x₀ ⟩) $ 𝔟 ≋ₐ 𝔞⟨ 𝔟 ⟩
  ƛη : ⁅ α ↣ β ⁆̣       ▹ ∅ ⊢      ƛ (𝔞 $ x₀) ≋ₐ 𝔞
```
`𝔐 : MCtx` is an inductively-defined metavariable context that can be converted to a sorted family of metavariables. It is constructed as a sequence of second-order metavariable type declarations `⁅ Π₁ ⊩ τ₁ ⁆ ⁅ Π₂ ⊩ τ₂ ⁆ … ⁅ Πₙ ⊩ τₙ ⁆̣`, where `τ` is the type of the metavariable and `Π` is the context of its parameters. Note that the last closing bracket must be `⁆̣`. The `Π ⊩ ` prefix can be omitted if the parameter context is empty, as in the case of `ƛη`
 and the second metavariable of `ƛβ` above. Metavariables are referred to by the alphabetic de Bruijn indices `𝔞`, `𝔟`, etc., and parameters are specified between angle brackets `⟨…⟩` attached to the metavariable. Object variables are given by numeric de Bruijn indices `x₀`, `x₁`, etc. The axioms may themselves be in a nonempty object variable context, such as in the case of partial differentiation.

#### Equational reasoning
The equational reasoning library generated from the axioms allows one to prove equalities through a sequence of rewrite steps, including:

* application of an axiom with a particular instantiation of metavariables;
* application of a derived equation with a particular instantiation of metavariables;
* application of a rewrite step on a subexpression (congruence);
* application of a definitional or propositional equality.

For example, below is the proof that the partial derivative of a variable with respect to itself is 1, expressed using the syntax and axiomatisation of [partial differentiation](out/PDiff/Equality.agda):

```agda
∂id : ⁅⁆ ▹ ⌊ * ⌋ ⊢ ∂₀ x₀ ≋ 𝟙
∂id = begin
  ∂₀ x₀        ≋⟨ cong[ thm 𝟘U⊕ᴿ with《 x₀ 》 ]inside ∂₀ ◌ᵃ ⟩ₛ
  ∂₀ (x₀ ⊕ 𝟘)  ≋⟨ ax ∂⊕ with《 𝟘 》 ⟩
  𝟙            ∎
```
* Like in standard Agda-style equational reasoning, the proof begins with `begin` and ends with `∎`, and proof steps are written in `≋⟨ E ⟩` between the terms (or `≋⟨ E ⟩ₛ` for symmetric rewrite).

* The `cong[ E ]inside C` step applies the equality `E` to a subexpression of the term specified by the congruence context `C`, which is just another term with an extra metavariable that can be used to denote the 'hole' in which the congruence is applied. Instead of `𝔞`, `𝔟`, the hole metavariable can be denoted `◌ᵃ`, `◌ᵇ`, etc. to make its role clear. For example, above we apply the right unit law under the partial differentiation operator `∂₀`.

* The `ax A with《 t₁ ◃ t₂ ◃ … ◃ tₙ 》` step applies an instance of axiom `A` with its metavariables `𝔞`, `𝔟`, …, `𝔫` instantiated with terms `t₁`, `t₂`, …, `tₙ` -- for example, above we apply the derivative-of-sum axiom `∂⊕ : ⁅ * ⁆̣ ▹ ⌊ * ⌋ ⊢ ∂₀ (x₀ ⊕ 𝔞) ≋ₐ 𝟙` with the metavariable `𝔞` set to the term `𝟘`.

* The `thm T with《 t₁ ◃ t₂ ◃ … ◃ tₙ 》` step is similar to the axiom step, except `T` is an established/derived equality, rather than an axiom. For example, the right unit law of commutative rings `𝟘U⊕ᴿ` is derived from the left unit law `𝟘U⊕ᴸ` and the commutativity of `⊕`, so it is applied as a theorem, rather than an axiom. A theorem without any metavariables (such as `∂id` itself) can be applied as `thm T`.

As another example, consider the derivation of the right distributivity of `⊗` over `⊕` from the left distributivity and commutativity of `⊗`. It shows the use of the double congruence step `cong₂[ E₁ ][ E₂ ]inside C`, where `C` can contain two hole metavariables.

```agda
⊗D⊕ᴿ : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (𝔞 ⊕ 𝔟) ⊗ 𝔠 ≋ (𝔞 ⊗ 𝔠) ⊕ (𝔟 ⊗ 𝔠)
⊗D⊕ᴿ = begin
  (𝔞 ⊕ 𝔟) ⊗ 𝔠       ≋⟨ ax ⊗C with《 𝔞 ⊕ 𝔟 ◃ 𝔠 》 ⟩
  𝔠 ⊗ (𝔞 ⊕ 𝔟)       ≋⟨ ax ⊗D⊕ᴸ with《 𝔠 ◃ 𝔞 ◃ 𝔟 》 ⟩
  (𝔠 ⊗ 𝔞) ⊕ (𝔠 ⊗ 𝔟)  ≋⟨ cong₂[ ax ⊗C with《 𝔠 ◃ 𝔞 》 ][ ax ⊗C with《 𝔠 ◃ 𝔟 》 ]inside ◌ᵈ ⊕ ◌ᵉ ⟩
  (𝔞 ⊗ 𝔠) ⊕ (𝔟 ⊗ 𝔠)  ∎
```

A property of [first-order logic](out/FOL/Equality.agda) is pushing a conjoined proposition under a universal quantifier from the right, derivable from the commutativity of `∧` and the analogous left-hand side property. The proof proceeds by commuting the conjunction, applying the left-side property, then commuting back under the universal quantifier. Importantly, to be able to apply commutativity to the term `𝔟 ∧ 𝔞⟨ x₀ ⟩` (which contains a free variable bound by the outside quantifier), we need to make `x₀` 'available' in the hole by writing `∀′ (◌ᶜ⟨ x₀ ⟩)` for the congruence context (rather than simply `∀′ ◌ᶜ`).
```agda
∧P∀ᴿ : ⁅ N ⊩ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (∀′ (𝔞⟨ x₀ ⟩)) ∧ 𝔟 ≋ ∀′ (𝔞⟨ x₀ ⟩ ∧ 𝔟)
∧P∀ᴿ = begin
  (∀′ (𝔞⟨ x₀ ⟩)) ∧ 𝔟   ≋⟨ ax ∧C with《 ∀′ (𝔞⟨ x₀ ⟩) ◃ 𝔟 》 ⟩
  𝔟 ∧ (∀′ (𝔞⟨ x₀ ⟩))   ≋⟨ ax ∧P∀ᴸ with《 𝔟 ◃ 𝔞⟨ x₀ ⟩ 》 ⟩
  ∀′ (𝔟 ∧ 𝔞⟨ x₀ ⟩)     ≋⟨ cong[ ax ∧C with《 𝔟 ◃ 𝔞⟨ x₀ ⟩ 》 ]inside ∀′ (◌ᶜ⟨ x₀ ⟩) ⟩
  ∀′ (𝔞⟨ x₀ ⟩ ∧ 𝔟)     ∎
```

For computational calculi like the STLC, equalities correspond to βη-equivalence of terms (assuming both axioms are given). For example, given the derived terms
```agda
plus : Λ 𝔛 (N ↣ N ↣ N) Γ
plus = ƛ (ƛ (nrec x₁ x₀ (su x₀)))

uncurry : Λ 𝔛 ((α ↣ β ↣ γ) ↣ (α ⊗ β) ↣ γ) Γ
uncurry = ƛ ƛ x₁ $ fst x₀ $ snd x₀
```
we can give an equational proof that `uncurry $ plus $ ⟨ su ze , su (su ze) ⟩ ≋ su (su (su ze))`. We first give a variant of β-reduction for double abstraction, which will allow us to apply `plus` and `uncurry` to both terms in one step.
```agda
ƛβ² : ⁅ β · α ⊩ γ ⁆ ⁅ α ⁆ ⁅ β ⁆̣ ▹ ∅
    ⊢ (ƛ (ƛ 𝔞⟨ x₀ ◂ x₁ ⟩)) $ 𝔟 $ 𝔠 ≋ 𝔞⟨ 𝔠 ◂ 𝔟 ⟩
ƛβ² = begin
      (ƛ (ƛ 𝔞⟨ x₀ ◂ x₁ ⟩)) $ 𝔟 $ 𝔠
  ≋⟨ cong[ ax ƛβ with《 (ƛ 𝔞⟨ x₀ ◂ x₁ ⟩) ◃ 𝔟 》 ]inside ◌ᵈ $ 𝔠 ⟩
      (ƛ 𝔞⟨ x₀ ◂ 𝔟 ⟩) $ 𝔠
  ≋⟨ ax ƛβ with《 (𝔞⟨ x₀ ◂ 𝔟 ⟩) ◃ 𝔠 》 ⟩
      𝔞⟨ 𝔠 ◂ 𝔟 ⟩
  ∎
```

Then, the calculational proof is as follows:
```agda
1+2 : ⁅⁆ ▹ ∅ ⊢ uncurry $ plus $ ⟨ su ze , su (su ze) ⟩ ≋ su (su (su ze))
1+2 = begin
      uncurry $ plus $ ⟨ su ze , su (su ze) ⟩
  ≋⟨ thm ƛβ² with《 x₁ $ fst x₀ $ snd x₀ ◃ plus ◃ ⟨ su ze , su (su ze) ⟩ 》 ⟩
      plus $ fst ⟨ su ze , su (su ze) ⟩ $ snd ⟨ su ze , su (su ze) ⟩
  ≋⟨ cong₂[ ax fβ with《 su ze ◃ su (su ze) 》 ][
            ax sβ with《 su ze ◃ su (su ze) 》 ]inside plus $ ◌ᵃ $ ◌ᵇ ⟩
      plus $ su ze $  su (su ze)
  ≋⟨ thm ƛβ² with《 nrec x₁ x₀ (su x₀) ◃ su ze ◃ su (su ze) 》 ⟩
      nrec (su ze) (su (su ze)) (su x₀)
  ≋⟨ ax suβ with《 su (su ze) ◃ su x₀ ◃ ze 》 ⟩
      su (nrec ze (su (su ze)) (su x₀))
  ≋⟨ cong[ ax zeβ with《 su (su ze) ◃ su x₀ 》 ]inside su ◌ᵃ ⟩
      su (su (su ze))
  ∎
```


### Additional features

#### Derived constructions

Surrounding a type, term, or equation with `{…}` marks it as a derived construct: instead of being added to the inductive declaration of types, terms, or axioms, it is listed as an Agda value declaration of the appropriate Agda type, with `?` in place of the implementation. For example, a `let`-declaration can be desugared to application, so instead of adding it as a separate operator, we mark it (along with its equational property) as derived:
```txt
syntax STLC | Λ

type
  N   : 0-ary
  _↣_ : 2-ary | r30

term
  app  : α ↣ β   α  ->  β       | _$_ l20
  lam  : α.β        ->  α ↣ β   | ƛ_  r10
 {letd : α  α.β     ->  β}  

theory
  (ƛβ) b : α.β  a : α |> app (lam(x.b[x]), a) = b[a]
  (ƛη) f : α ↣ β      |> lam (x. app(f, x))   = f
 {(lβ) b : α.β  a : α |> letd (a, x.b[x])     = b[a]}
```

This will compile to the Agda declaration
```agda
-- Derived operations
letd : Λ 𝔛 α Γ → Λ 𝔛 β (α ∙ Γ) → Λ 𝔛 β Γ
letd = ?
```
that can be implemented by hand (as `letd a b = (ƛ b) $ a`), and similarly for the 'theorem'
```agda
-- Derived equations
lβ : ⁅ α ⊩ β ⁆ ⁅ α ⁆̣ ▹ ∅ ⊢ letd 𝔟 (𝔞⟨ x₀ ⟩) ≋ 𝔞⟨ 𝔟 ⟩
lβ = ?
```
that can be implemented as `lβ = ax ƛβ with《 𝔞⟨ x₀ ⟩ ◃ 𝔟 》` since the declaration desugars (definitionally) to an application.

It is possible for not derived constructs to depend on derived ones. For example, the axiomatisation of [partial differentiation](gen/ex/misc/pdiff) involves the special cases of differentiation with respect to the first and second variable. We mark them as operations derived from `pdiff`, and use them as normal in the axioms:

```
term
  pdiff : *.*  *  ->       * | ∂_∣_
 {d0    :     *.* ->     *.* | ∂₀_}
 {d1    : (*,*).* -> (*,*).* | ∂₁_}

theory
  (∂⊕) a : * |> x : * |- d0 (add (x, a)) = one
  (∂⊗) a : * |> x : * |- d0 (mult(a, x)) = a
  ...
```
Note also that derived operations (like `d0` and `d1`) may have return sorts in an extended context, since they are defined by the user, rather than extracted from the generic framework. Non-derived operators must have return types without bound variables.

#### Algebraic properties

The library is also very suitable for reasoning about unsorted and first-order syntaxes, such as algebraic structures. While the full power of the generated metatheory is not needed (e.g. variable capture is not possible without binders), the notions of term- and equation-in-context and the equational reasoning framework are applicable. Furthermore, many second-order syntaxes are minor extensions of first-order ones (first-order logic is propositional logic extended with quantifiers, the axiomatisation of partial differentiation involves extending a commutative ring with a partial differentiation operation) so results about the first-order fragments can be transferred to the extended settings.

It is straightforward to capture algebraic structures such as monoids in a syntax description:

```
syntax Monoid | M

term
  unit :         * | ε
  add  : *  * -> * | _⊕_ l20

theory
  (εU⊕ᴸ) a     |> add (unit, a) = a
  (εU⊕ᴿ) a     |> add (a, unit) = a
  (⊕A)   a b c |> add (add(a, b), c) = add (a, add(b, c))
```
The lack of a `type` declaration marks the syntax as un(i)sorted with sort `*`. For convenience, standard algebraic properties like unit laws and associativity are predefined in the library, so we can instead write:
```
syntax Monoid | M

term
  unit :         * | ε
  add  : *  * -> * | _⊕_ l20

theory
  'unit' unit of 'add'
  'add'  associative
```
The two properties internally desugar to the explicitly written axioms. The supported properties are listed below, where `op0`, `op1` and `op2` denote constants, unary and binary operators, respectively.

* `'op2' associative, commutative, idempotent, involutive`
* `'op0' [left|right] unit of 'op2'`
* `'op0' [left|right] annihilates 'op2'`
* `'op1' [left|right] inverse of 'op2' with 'op0'` (`op1` is the inverse/negation operator, `op0` is the unit)
* `'op2' [left|right] distributes over 'op2'`
* `'op2' [left|right] absorbs 'op2'`
* `'op2' and 'op2' absorptive` (both operators absorb each other)

Several properties may be directed: left unit, right distributivity, etc. If the corresponding binary operator is commutative, the directions are interderivable. In this case, the library will only list the left direction as an axiom, and generates the derivation of the right axiom automatically. Thus, for a commutative monoid
```
syntax CommMonoid | CM

term
  unit :         * | ε
  add  : *  * -> * | _⊕_ l20

theory
  'unit' unit of 'add'
  'add'  associative, commutative
```
the generated axioms will only include the left unit law
```agda
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ CM) α Γ → (𝔐 ▷ CM) α Γ → Set where
  εU⊕ᴸ : ⁅ * ⁆̣             ▹ ∅ ⊢       ε ⊕ 𝔞 ≋ₐ 𝔞
  ⊕A   : ⁅ * ⁆ ⁅ * ⁆ ⁅ * ⁆̣ ▹ ∅ ⊢ (𝔞 ⊕ 𝔟) ⊕ 𝔠 ≋ₐ 𝔞 ⊕ (𝔟 ⊕ 𝔠)
  ⊕C   : ⁅ * ⁆ ⁅ * ⁆̣       ▹ ∅ ⊢       𝔞 ⊕ 𝔟 ≋ₐ 𝔟 ⊕ 𝔞
```
and the derivation of `εU⊕ᴿ` is predefined:
```agda
εU⊕ᴿ : ⁅ * ⁆̣ ▹ ∅ ⊢ 𝔞 ⊕ ε ≋ 𝔞
εU⊕ᴿ = tr (ax ⊕C with《 𝔞 ◃ ε 》) (ax εU⊕ᴸ with《 𝔞 》)
```
In fact, the right distributivity example `⊗D⊕ᴿ` given in [Equational reasoning](#equational-reasoning) is automatically derived from left distributivity and commutativity of `⊗`.
This saves a lot of boilerplate defining symmetric versions of properties for commutative operators.

#### Module system
The syntax description language implements an Agda-like module system for extending and combining syntaxes. This is very convenient for building up algebraic hierarchies or adding new constructs to computational calculi.

Building on top of an existing base syntax is done using the `extends` keyword. In the simplest case, the keyword is followed by a comma-separated list of file names that get recursively interpreted first and combined with the new constructs. For example, a group is a monoid with an inverse operator:
```
syntax Group | G extends monoid

term
  neg : * -> * | ⊖_  r40

theory
  'neg' inverse of 'add' with 'unit'
```

By describing the introduction and elimination terms, and βη-equivalence rules of computational constructs independently, we can extend a base syntax (like STLC) with any number of new types and operations and 'mix and match' language features as we wish. For example, the 'typed λ-calculus' is the extension of the simply typed λ-calculus with products, sums, unit and empty types, and natural numbers (which are individually described in their respective files):
```
syntax TLC | Λ extends stlc, unit, prod, empty, sum, nat
```
This is equivalent to the following syntax description:
```
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
  (zeβ) z : α   s : (α,N).α        |> nrec (ze,     z, r m. s[r,m]) = z
  (suβ) z : α   s : (α,N).α  n : N |> nrec (su (n), z, r m. s[r,m])
                                    = s[nrec (n, z, r m. s[r,m]), n]
```

We can have more control over what names we import and how via the `hiding`, `using`, `deriving` and `renaming` modifiers. In these cases, the imports are listed one-by-one in the `syntax` block with the modifiers (separated by `;`) in parentheses. For example:
```
syntax Ext extends
  - syn1 (using op1, op2, eq3; renaming eq1 to ax1; deriving eq3)
  - syn2 (hiding eq2; renaming op0:ε to const:c, op3:⊗ to op4:⊠:l40)
```
The first line imports the operators `op1` and `op2` (and their corresponding symbols, if they exist) and axiom `eq`, renames `eq1` to `ax1`, and marks `eq3` as a derivable property (presumably using the new axioms of the `Ext` module). The second line imports everything (types, operators, symbols, equations) other than `eq2`, and gives `op0` and `op3` new names: `op0` and its symbol `ε` get renamed to `const` and `c` respectively, while `op3` and `⊗` get renamed to `op4` and `⊠` with the fixity of `⊠` changed to `l40`. The renaming of symbols also extends to occurrences of symbols in axiom names: for example, an axiom like `εU⊕ᴸ` in `syn2` would automatically be renamed to `cU⊠ᴸ` in `Ext`.

As a concrete example, consider the algebraic structure of a semiring,  consisting of a commutative (additive) monoid and a second (multiplicative) monoid satisfying two-way distributivity and annihilation. This 'recipe' can be concisely expressed using imports, renaming of names and symbols, and property specifications:
```
syntax Semiring | SR extends
  - cmonoid (renaming unit:ε to zero:𝟘)
  - monoid  (renaming unit:ε to one:𝟙, add:⊕ to mult:⊗:l30)

theory
  'mult' distributes over 'add'
  'zero' annihilates 'mult'
```
The resulting description is equivalent to the following, with `𝟘U⊕ᴿ` derived automatically:
```
syntax Semiring | SR

type
  * : 0-ary

term
  zero : * | 𝟘
  add  : *  *  ->  * | _⊕_ l20
  one  : * | 𝟙
  mult : *  *  ->  * | _⊗_ l30

theory
  (𝟘U⊕ᴸ) a |> add (zero, a) = a
  (𝟘U⊕ᴿ) a |> add (a, zero) = a
  (⊕A)   a b c |> add (add(a, b), c) = add (a, add(b, c))
  (⊕C)   a b |> add(a, b) = add(b, a)
  (𝟙U⊗ᴸ) a |> mult (one, a) = a
  (𝟙U⊗ᴿ) a |> mult (a, one) = a
  (⊗A)   a b c |> mult (mult(a, b), c) = mult (a, mult(b, c))
  (⊗D⊕ᴸ) a b c |> mult (a, add (b, c)) = add (mult(a, b), mult(a, c))
  (⊗D⊕ᴿ) a b c |> mult (add (a, b), c) = add (mult(a, c), mult(b, c))
  (𝟘X⊗ᴸ) a |> mult (zero, a) = zero
  (𝟘X⊗ᴿ) a |> mult (a, zero) = zero
```
This may be further extended to rings and commutative rings as follows:
```
syntax Ring | R extends semiring

term
  neg : * ->  * | ⊖_ r50

theory
  'neg' inverse of 'add' with 'zero'
```

```
syntax CommRing | CR extends ring

theory
  'mult' commutative
```
The equational theory corresponding to commutative rings only includes left-side axioms, since every right-side property (unit laws, annihilation law, distributivity, negation) is derived automatically.
