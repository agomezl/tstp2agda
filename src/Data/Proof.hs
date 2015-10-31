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


data ProofTreeGen a = Axiom  a
                    | Conj    a
                    | Intro   a
                    | Strip   a [ProofTreeGen a]
                    | Simp    a [ProofTreeGen a]
                    | Neg     a [ProofTreeGen a]
                    | Canno   a [ProofTreeGen a]
                    | New     a [ProofTreeGen a]
                    | Unknown a
                 deriving (Eq,Ord,Show)
type ProofTree = ProofTreeGen String

instance Functor ProofTreeGen where
    fmap f (Axiom   a)   = Axiom   (f a)
    fmap f (Conj    a)   = Conj    (f a)
    fmap f (Intro   a)   = Intro   (f a)
    fmap f (Strip   a t) = Strip   (f a) (map (fmap f) t)
    fmap f (Simp    a t) = Simp    (f a) (map (fmap f) t)
    fmap f (Neg     a t) = Neg     (f a) (map (fmap f) t)
    fmap f (Canno   a t) = Canno   (f a) (map (fmap f) t)
    fmap f (New     a t) = New     (f a) (map (fmap f) t)
    fmap f (Unknown a)   = Unknown (f a)

instance Foldable ProofTreeGen where
    foldr f b (Axiom   a)    = f a b
    foldr f b (Conj    a)    = f a b
    foldr f b (Intro   a)    = f a b
    foldr f b (Strip   a t)  = f a $ foldr (flip $ foldr f) b t
    foldr f b (Simp    a t)  = f a $ foldr (flip $ foldr f) b t
    foldr f b (Neg     a t)  = f a $ foldr (flip $ foldr f) b t
    foldr f b (Canno   a t)  = f a $ foldr (flip $ foldr f) b t
    foldr f b (New     a t)  = f a $ foldr (flip $ foldr f) b t
    foldr f b (Unknown a)    = f a b

instance Traversable ProofTreeGen where
    traverse f (Axiom   a)    = Axiom   <$> f a
    traverse f (Conj    a)    = Conj    <$> f a
    traverse f (Intro   a)    = Intro   <$> f a
    traverse f (Strip   a t)  = Strip   <$> f a <*> traverse (traverse f) t
    traverse f (Simp    a t)  = Simp    <$> f a <*> traverse (traverse f) t
    traverse f (Neg     a t)  = Neg     <$> f a <*> traverse (traverse f) t
    traverse f (Canno   a t)  = Canno   <$> f a <*> traverse (traverse f) t
    traverse f (New     a t)  = New     <$> f a <*> traverse (traverse f) t
    traverse f (Unknown a)    = Unknown <$> f a





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
