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

import Data.TSTP     (F(..),Formula(..),Source(..),Role(..),isBottom)
import Data.Map as M (lookup)
import Data.Proof    (ProofMap,getParents)
import Data.List     (isPrefixOf)
import Util          ((▪),βshow)

-- Single function signature
-- | An
-- <http://wiki.portal.chalmers.se/agda/pmwiki.php Agda>
-- type signature @α : τ@
data AgdaSignature = Signature String [Formula]
                   -- ^ Regular top level signature
                   | ScopedSignature String [Formula]
                   -- ^ Fully scoped signature with no newly
                   -- introduced type variables

                  deriving (Eq)

-- | Given a proof map ω and some formula name φ, construct
-- the appropriated 'AgdaSignature' based on the parents of φ
buildSignature ∷ ProofMap → String → Maybe AgdaSignature
buildSignature ω φ | "subgoal" `isPrefixOf` φ = Nothing
                   | "negate"  `isPrefixOf` φ = Nothing
                   | otherwise = do
  φ₁@(F _ γ ζ β) ← M.lookup φ ω
  let ρ = case β of
            Inference _ _ ρ₁ → map formula $ getParents ω ρ₁
            _                → []
  if elem γ [Axiom,Conjecture]
  then Nothing
  else return $ Signature ("fun-" ++ φ) (ρ ++ [ζ])

-- | Retrieve signature name
fname ∷ AgdaSignature → String
fname (Signature       a _) = a
fname (ScopedSignature a _) = a

-- Pretty prints an `AgdaSignature`
instance Show AgdaSignature where
    show (Signature α ρ)       = α ▪ ":" ▪ ρ
    show (ScopedSignature α (x:xs)) = α ▪ ":" ▪ ρ
        where ρ = foldl ((▪) . (▪ '→')) (βshow x) xs

instance Ord AgdaSignature where
    a <= b = fname a <= fname b
