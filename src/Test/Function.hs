{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Function
-- Author : Alejandro Gomez
-- Date   : Wed Oct 28 11:11:25 2015
-- Description :
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------
module Test.Function where

import Data.TSTP
import Test.Proof

func1 ∷ [Formula]
func1 = do
  f ← base1
  return . formula $ f
