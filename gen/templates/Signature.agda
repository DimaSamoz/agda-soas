{-
This file was created from the following second-order syntax description:

$sig_string
-}

module ${syn_name}.Signature where

open import SOAS.Context

-- Type declaration
data $type : Set where
  $type_decl
$type_fixity
open import SOAS.Syntax.Signature $type public
open import SOAS.Syntax.Build $type public

-- Operator symbols
data ${sig}ₒ : Set where
  $operator_decl

-- Term signature
${sig}:Sig : Signature ${sig}ₒ
${sig}:Sig = sig λ
  { $sig_decl
  }

open Signature ${sig}:Sig public
