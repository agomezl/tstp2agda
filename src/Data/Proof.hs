{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : ProofTree
-- Author : Alejandro Gómez-Londoño
-- Date   : Mon Oct 12 14:10:57 2015
-- Description : Proof tree data structure
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------
module Data.Proof where

import Data.Map (Map)
import Data.Map as M (lookup)
import Data.Maybe (catMaybes)
import Data.TSTP (Formula(..),Rule(..),F(..),Parent(..),Source(..))
import qualified Data.TSTP as R (Role(..))

data ProofTree = Axiom   String
               | Intro   String
               | Simp    String [ProofTree]
               | Neg     String [ProofTree]
               | Canno   String [ProofTree]
               | New     String [ProofTree]
               | Unknown String
                 deriving (Eq,Ord,Show)

type ProofMap = Map String F

buildProofTree ∷ ProofMap → F → ProofTree
buildProofTree _ (F n R.Axiom _ _) = Axiom n
buildProofTree m (F n R.Plain _ s) = caseSrc s
    where caseSrc  (Inference r _ p) = caseRule r
              where caseRule Simplify     = Simp  n parents
                    caseRule Negate       = Neg   n parents
                    caseRule Canonicalize = Canno n parents
                    caseRule (NewRule s)  = New   n parents
                    parents               = getParents m p
          caseSrc  _                      = unknownMsg
          unknownMsg =  unknownTree "Source" s n
buildProofTree _ (F n r       _ _) = unknownTree "Role" r n

-- Utility functions

getParents ∷ ProofMap → [Parent] → [ProofTree]
getParents m p = map (buildProofTree m) parentsF
    where parentsF = catMaybes $ map (flip M.lookup $ m) parents
          parents = map (\(Parent s _) → s) p

unknownTree ∷ (Show a) ⇒ String → a → String → ProofTree
unknownTree m r n = Unknown $ m ++  ' ':show r  ++ " in " ++ n
