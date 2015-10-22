{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Core
-- Author : Alejandro Gómez-Londoño
-- Date   : Wed Oct  7 23:30:16 2015
-- Description : Core module of tstp2agda
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------

module T2A.Core where

import Data.TSTP (F(..),Formula(..),Source(..),Role(..))


type AgdaVariable = String
data AgdaType     = Set  |   -- regular set Set₁
                    Setℕ |   -- Setₙ
                    Γ String -- Any other type
                  deriving (Show, Ord, Eq)

data AgdaSignature = Signature {
      fname ∷ String,
      fconstraints ∷ [([AgdaVariable],AgdaType)],
      ftype ∷ [Formula]
    }