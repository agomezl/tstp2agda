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
import T2A.Core
import Data.Proof
import Data.Maybe (catMaybes)
import Data.Foldable (toList)


func1 ∷ [Formula]
func1 = do
  f ← base1
  return . formula $ f

map1 ∷ ProofMap
map1 = buildProofMap base1

tree1 ∷ ProofTree
tree1 = buildProofTree map1 (last base1)

signature1 ∷ [AgdaSignature]
signature1 = catMaybes . toList . fmap (buildSignature map1) $ tree1
