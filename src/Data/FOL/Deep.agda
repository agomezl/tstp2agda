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

------------------------------------------------------------------------------

open import Data.Bool public using (Bool; true; false; not)
open import Data.Bool public renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Fin  public using (Fin; zero; suc; #_)
open import Data.List public using (List; []; _∷_; _++_; [_])
open import Data.Vec  public using (Vec; lookup)

open import Function  public using (_$_)

------------------------------------------------------------------------------
