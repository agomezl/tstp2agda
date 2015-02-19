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


data Lang = Cnf | Fof

data F = F { lang ∷ Lang,
             name ∷ String,
             role ∷ Role,
             formula ∷ String,
             annotations ∷ String
           }
