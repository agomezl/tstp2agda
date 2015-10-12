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

import Data.Map (Map, empty, insert)
import Data.Map as M (lookup)
import Data.Maybe (catMaybes)
import Data.TSTP (Formula(..),F(..),Parent(..),Source(..))
import qualified Data.TSTP as R (Role(..),Rule(..))

data ProofTree = Axiom   String
               | Conj    String
               | Intro   String
               | Strip   String [ProofTree]
               | Simp    String [ProofTree]
               | Neg     String [ProofTree]
               | Canno   String [ProofTree]
               | New     String [ProofTree]
               | Unknown String
                 deriving (Eq,Ord,Show)

type ProofMap = Map String F

buildProofTree ∷ ProofMap → F → ProofTree
buildProofTree _ (F n R.Axiom _ _)      = Axiom n
buildProofTree _ (F n R.Conjecture _ _) = Conj n
buildProofTree m (F n R.Plain _ s)      = caseSrc s
    where caseSrc  (Inference r _ p) = caseRule r
              where caseRule R.Simplify     = Simp  n parents
                    caseRule R.Negate       = Neg   n parents
                    caseRule R.Canonicalize = Canno n parents
                    caseRule R.Strip        = Strip n parents
                    caseRule (R.NewRule s)  = New   n parents
                    parents               = getParents m p
          caseSrc  _                      = unknownMsg
          unknownMsg =  unknownTree "Source" s n
buildProofTree _ (F n r       _ _) = unknownTree "Role" r n

buildProofMap ∷ [F] → ProofMap
buildProofMap f = foldl buildMap empty f
    where buildMap m f' = insert (name f') f' m

-- Utility functions

getParents ∷ ProofMap → [Parent] → [ProofTree]
getParents m p = map (buildProofTree m) parentsF
    where parentsF = catMaybes $ map (flip M.lookup $ m) parents
          parents = map (\(Parent s _) → s) p

unknownTree ∷ (Show a) ⇒ String → a → String → ProofTree
unknownTree m r n = Unknown $ m ++  ' ':show r  ++ " in " ++ n
