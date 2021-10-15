------------------------------------------------------------------------
-- Second-order abstract syntax
--
-- Examples of the formalisation framework in use
------------------------------------------------------------------------


module Examples where

-- | Algebraic structures

-- Monoids
import Monoid.Signature
import Monoid.Syntax
import Monoid.Equality

-- Commutative monoids
import CommMonoid.Signature
import CommMonoid.Syntax
import CommMonoid.Equality

-- Groups
import Group.Signature
import Group.Syntax
import Group.Equality

-- Commutative groups
import CommGroup.Signature
import CommGroup.Syntax
import CommGroup.Equality

-- Group actions
import GroupAction.Signature
import GroupAction.Syntax
import GroupAction.Equality

-- Semirings
import Semiring.Signature
import Semiring.Syntax
import Semiring.Equality

-- Rings
import Ring.Signature
import Ring.Syntax
import Ring.Equality

-- Commutative rings
import CommRing.Signature
import CommRing.Syntax
import CommRing.Equality


-- | Logic

-- Propositional logic
import PropLog.Signature
import PropLog.Syntax
import PropLog.Equality

-- First-order logic (with example proofs)
import FOL.Signature
import FOL.Syntax
import FOL.Equality


-- | Computational calculi

-- Combinatory logic
import Combinatory.Signature
import Combinatory.Syntax
import Combinatory.Equality

-- Untyped λ-calculus
import UTLC.Signature
import UTLC.Syntax
import UTLC.Equality

-- Simply-typed λ-calculus (with operational semantics and environment model)
import STLC.Signature
import STLC.Syntax
import STLC.Equality
import STLC.Model

-- Typed λ-calculus with product and sum types, and naturals (with example derivation)
import TLC.Signature
import TLC.Syntax
import TLC.Equality

-- PCF
import PCF.Signature
import PCF.Syntax
import PCF.Equality


-- | Miscellaneous

-- Lenses
import Lens.Signature
import Lens.Syntax
import Lens.Equality

-- Inception algebras
import Inception.Signature
import Inception.Syntax
import Inception.Equality

-- Substitution algebras
import Sub.Signature
import Sub.Syntax
import Sub.Equality

-- Partial differentiation (with some example proofs)
import PDiff.Signature
import PDiff.Syntax
import PDiff.Equality
