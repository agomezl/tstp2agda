
-- | Function module

{-# LANGUAGE UnicodeSyntax #-}


module Test.Function where


import           Data.Foldable (toList)
import           Data.Maybe    (catMaybes)
import           Data.Proof    (base1)
import           Data.TSTP
import           T2A.Core
import           Test.Proof


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
