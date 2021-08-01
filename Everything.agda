
------------------------------------------------------------------------
-- Second-order abstract syntax
--
-- Formalisation of second-order abstract syntax with variable binding.
------------------------------------------------------------------------


module Everything where

-- Public exports of modules and definitions used throughout the library.
import SOAS.Common

-- Abstract categorical definitions of carrier categories with extra structure,
-- and associated free constructions.
import SOAS.Construction.Free
import SOAS.Construction.Structure

-- Skew monoidal and closed structure
import SOAS.Construction.Skew.SkewClosed

-- Add sorting to categories, and prove that various categorical
-- structure (CCC, monoidal, etc.) are preserved.
import SOAS.Sorting

-- Definition of simple contexts as lists of sorts.
import SOAS.Context

-- The sorted family of variables and generalised context maps
import SOAS.Variable


-- | Context maps as renamings, substitutions and category morphisms

-- Context map combinators
import SOAS.ContextMaps.Combinators

-- Category of contexts and renamings
import SOAS.ContextMaps.CategoryOfRenamings

-- Inductive context maps
import SOAS.ContextMaps.Inductive

-- Common properties of context maps
import SOAS.ContextMaps.Properties

-- | Families

-- Definition of the category of sorted families
import SOAS.Families.Core

-- Isomorphism between sorted families
import SOAS.Families.Isomorphism

-- Bi-Cartesian closed and linear monoidal closed structure of families
import SOAS.Families.BCCC
import SOAS.Families.Linear

-- Context extension endofunctor
import SOAS.Families.Delta

-- Inductive construction of families
import SOAS.Families.Build


-- | Abstract constructions

-- Box modality
import SOAS.Abstract.Box

-- □-coalgebra on families – renaming structure
import SOAS.Abstract.Coalgebra

-- Internal hom of families
import SOAS.Abstract.Hom

-- Closed monoid in families – substitution structure
import SOAS.Abstract.Monoid

-- Exponential strength
import SOAS.Abstract.ExpStrength


-- | Constructions built upon coalgebras

-- Coalgebraic maps 𝒳 ⇾ 〖𝒫 , 𝒴〗
import SOAS.Coalgebraic.Map

-- Lifting and strength
import SOAS.Coalgebraic.Lift
import SOAS.Coalgebraic.Strength

-- Monoids compatible with coalgebra structure
import SOAS.Coalgebraic.Monoid


-- | Metatheory for a second-order binding signature

-- Binding algebras
import SOAS.Metatheory.Algebra

-- Algebras with variables and metavariables
import SOAS.Metatheory.MetaAlgebra

-- Signature monoids
import SOAS.Metatheory.Monoid

-- Initial-algebra semantics
import SOAS.Metatheory.Semantics

-- Parametrised interpretations
import SOAS.Metatheory.Traversal

-- Renaming structure by initiality
import SOAS.Metatheory.Renaming

-- Coalgebraic maps by initiality
import SOAS.Metatheory.Coalgebraic

-- Substitution structure by initiality
import SOAS.Metatheory.Substitution

-- Free monoid structure
import SOAS.Metatheory.FreeMonoid

-- Syntactic structure
import SOAS.Metatheory.Syntax

-- | Second-order structure

-- Metasubstitution
import SOAS.Metatheory.SecondOrder.Metasubstitution

-- Unit of metasubstitution
import SOAS.Metatheory.SecondOrder.Unit

-- Equational theory
import SOAS.Metatheory.SecondOrder.Equality

-- | Term syntax of a second-order signature

-- Argument representation
import SOAS.Syntax.Arguments

-- Second-order binding signature
import SOAS.Syntax.Signature

-- Shorthand notation
import SOAS.Syntax.Shorthands

-- Signature construction
import SOAS.Syntax.Build

-- First-order term syntax
import SOAS.Syntax.Term
