{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : TSTP
-- Author : Alejandro Gómez Londoño
-- Date   : Wed Feb 11 00:29:30 2015
-- Description : TSPT Data Types
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------

module Data.TSTP where
import Codec.TPTP.Base (BinOp,Quant,InfixPred,V,AtomicWord,Annotations)

data Role = Axiom
          | Hypothesis
          | Definition
          | Assumption
          | Lemma
          | Theorem
          | Conjecture
          | NegatedConjecture
          | Plain
          | FiDomain
          | FiFunctors
          | FiPredicates
          | Type
          | Unknown

data F = F { name ∷ String,
             role ∷ Role,
             formula ∷ Formula,
             annotations ∷ Annotations
           }

-- * General decorated formulae and terms

-- The following code is based on:
-- https://github.com/DanielSchuessler/logic-TPTP
-- and is just a simplified version of the the datatypes
-- (without the Indirect composite)

data Formula = BinOp Formula BinOp Formula    -- ^ Binary connective application
             | InfixPred Term InfixPred Term  -- ^ Infix predicate application
             | PredApp AtomicWord [Term]      -- ^ Predicate application
             | Quant Quant [V] Formula        -- ^ Quantified Formula
             | (:~:) Formula                  -- ^ Negation
             deriving (Eq,Ord,Show,Read)

data Term = Var V                             -- ^ Variable
          | NumberLitTerm Rational            -- ^ Number literal
          | DistinctObjectTerm String         -- ^ Double-quoted item
          | FunApp AtomicWord [Term]          -- ^ Function symbol application
                                              -- (constants are encoded as
                                              -- nullary functions)
          deriving (Eq,Ord,Show,Read)
