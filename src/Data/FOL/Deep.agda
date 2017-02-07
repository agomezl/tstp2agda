open import Data.Nat using (ℕ)

------------------------------------------------------------------------------
-- Deep Embedding : Propositional Logic
------------------------------------------------------------------------------

-- This module requires the number of atoms in the formula.
-- This number is the parameter n
module Data.FOL.Deep (n : ℕ) where

-- Definition of connectives and ⊢ relation.
open import Data.FOL.Deep.Syntax n public

-- Valuation and ⊨ relation.
open import Data.FOL.Deep.Semantics n public

-- Some lemmas and common theorems.
open import Data.FOL.Deep.Theorems n public
