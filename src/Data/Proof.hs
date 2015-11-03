{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE CPP #-}
--------------------------------------------------------------------------------
-- File   : ProofTree
-- Author : Alejandro Gómez-Londoño
-- Date   : Mon Oct 12 14:10:57 2015
-- Description : Proof tree data structure
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------
#ifndef MIN_VERSION_base
#define MIN_VERSION_base(a,b,c) 1
#endif
-- Assume we are using the newest versions when using ghci without cabal
module Data.Proof where

import Data.Map (Map, empty, insert)
import Data.Map as M (lookup)
import Data.Maybe (catMaybes)
import Data.TSTP (Formula(..),F(..),Parent(..),Source(..))
import qualified Data.TSTP as R (Role(..),Rule(..))
#if MIN_VERSION_base(4,7,0)
import Prelude hiding (foldr,foldl)
import Control.Applicative ((<$>),(<*>))
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
#endif

data ProofTreeGen a = Leaf R.Role a
                    | Root R.Rule a [ProofTreeGen a]
                      deriving (Eq,Ord,Show)

type ProofTree = ProofTreeGen String

instance Functor ProofTreeGen where
    fmap f (Leaf r a)   = Leaf r (f a)
    fmap f (Root r a t) = Root r (f a) (map (fmap f) t)

instance Foldable ProofTreeGen where
    foldr f b (Leaf r a)    = f a b
    foldr f b (Root r a t)  = f a $ foldr (flip $ foldr f) b t

instance Traversable ProofTreeGen where
    traverse f (Leaf r a)    = Leaf r <$> f a
    traverse f (Root r a t)  = Root r <$> f a <*> traverse (traverse f) t

type ProofMap = Map String F

buildProofTree ∷ ProofMap → F → ProofTree
buildProofTree _ (F n R.Axiom _ _)      = Leaf R.Axiom n
buildProofTree _ (F n R.Conjecture _ _) = Leaf R.Conjecture n
buildProofTree m (F n R.Plain _ s)      = caseSrc s
    where caseSrc  (Inference r _ p) = let parents = getParentsTree m p
                                       in Root r n parents
          caseSrc  _                 = unknownMsg
          unknownMsg                 = unknownTree "Source" s n
buildProofTree _ (F n r       _ _)      = unknownTree "Role" r n

buildProofMap ∷ [F] → ProofMap
buildProofMap f = foldl buildMap empty f
    where buildMap m f' = insert (name f') f' m

-- Utility functions

getParentsTree ∷ ProofMap → [Parent] → [ProofTree]
getParentsTree m p = map (buildProofTree m) $ getParents m p

getParents ∷ ProofMap → [Parent] → [F]
getParents ω ρ = catMaybes $ map (flip M.lookup $ ω) parents
    where parents  = map (\(Parent s _) → s) ρ

unknownTree ∷ (Show a) ⇒ String → a → String → ProofTree
unknownTree m r n = Leaf R.Unknown $ m ++  ' ':show r  ++ " in " ++ n
