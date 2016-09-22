
-- | Data.Proof module

{-# LANGUAGE CPP           #-}
{-# LANGUAGE UnicodeSyntax #-}


#ifndef MIN_VERSION_base
#define MIN_VERSION_base(a,b,c) 1
#endif
-- Assume we are using the newest versions when using ghci without cabal


module Data.Proof
  ( -- * Types
    ProofTreeGen(..)
  , ProofMap
  , ProofTree
  , IdSet
  -- * Constructors
  , buildProofMap
  , buildProofTree
  -- * Internals
  , getParents
  , getParentsTree
  , unknownTree
  ) where

import           Data.Map            (Map, empty, insert)
import           Data.Map            as M (lookup)
import           Data.Maybe          (catMaybes, mapMaybe)
import           Data.Set            (Set)

import  Data.TSTP
  ( F (..)
  , Formula (..)
  , Parent (..)
  , Role (..)
  , Rule (..)
  , Source (..)
  )

#if __GLASGOW_HASKELL__ <= 708
import           Control.Applicative ((<$>), (<*>))
import           Data.Foldable       (Foldable (..))
import           Data.Traversable    (Traversable (..))
import           Prelude             hiding (foldl, foldr)
#endif

-- | Generic tree structure for representing the structure of a proof.
data ProofTreeGen a =
    -- | 'Leaf' 'r' 'a' is a node with 'Role' 'r' and content 'a' (usually
    -- 'String', 'F' or 'Formula') and with no dependencies in other nodes.
    Leaf Role a |
    -- | 'Root' 'r' 'a' 'd' is a node with deduction 'Rule' 'r', content 'a'
    -- (usually 'String', 'F' or 'Formula'),  and dependencies 'd'.
    Root Rule a [ProofTreeGen a]
         deriving (Eq,Ord,Show)

-- | Simple type for sets of identifiers whit associated scopes
type IdSet = Set (Int,String)

-- | Concrete instance of 'ProofTreeGen' with 'String' as
-- contents. Each node contains the name of a corresponding formula,
-- along with its dependencies.
type ProofTree = ProofTreeGen String

instance Functor ProofTreeGen where
    fmap f (Leaf r a)   = Leaf r (f a)
    fmap f (Root r a t) = Root r (f a) (map (fmap f) t)

instance Foldable ProofTreeGen where
    foldr f b (Leaf r a)   = f a b
    foldr f b (Root r a t) = f a $ foldr (flip $ foldr f) b t

instance Traversable ProofTreeGen where
    traverse f (Leaf r a)   = Leaf r <$> f a
    traverse f (Root r a t) = Root r <$> f a <*> traverse (traverse f) t

-- | 'Map' from formula names to an 'F' formula type, useful to get more
-- information from a node in a 'ProofTree'.
type ProofMap = Map String F

-- | 'buildProofTree' 'm' 'f', build a 'ProofTree' with 'f' as root,
-- and using 'm' for dependencies resolution. Depending on the root,
-- not all values in 'm' are used.
buildProofTree ∷ ProofMap     -- ^ 'Map' for resolving dependencies
               → F            -- ^ Root formula
               → ProofTree    -- ^ Tree of formulas with the given
                              -- formula as root
buildProofTree m formulaF =
  let namef ∷ String
      namef = name formulaF
  in case role formulaF of
    Axiom       → Leaf Axiom namef
    Conjecture  → Leaf Conjecture namef
    Plain       → case source formulaF of
      (Inference r _ p) → Root r namef (getParentsTree m p)
      sname       → unknownTree "Source" sname namef
    rname         →  unknownTree "Role" rname namef

-- | 'buildProofMap' 'lf', given a list of functions 'lf' builds a 'ProofMap'
buildProofMap ∷ [F]      -- ^ List of functions
              → ProofMap -- ^ Map of the given functions indexed by its names
buildProofMap = foldl buildMap empty
    where
      buildMap m f' = insert (name f') f' m

-- | 'getParentsTree' 'm' 'p', from a 'Map' 'm' and a list of parents 'p'
-- return a list of corresponding parent subtrees.
getParentsTree ∷ ProofMap    -- ^ 'Map'
               → [Parent]    -- ^ List of parents
               → [ProofTree] -- ^ List of parents subtrees
getParentsTree m p = map (buildProofTree m) $ getParents m p

-- | 'getParents' 'm' 'p', from a 'Map' 'm' and a list of parents 'p'
-- returns a list of corresponding parent formulas.
getParents ∷ ProofMap -- ^ 'Map'
           → [Parent] -- ^ List of 'Parents
           → [F]      -- ^ List of parent formulas
getParents ω ρ = mapMaybe (`M.lookup` ω) parents
    where
      parents  = map (\(Parent s _) → s) ρ

-- | When an unknown 'Rule', 'Source', or other unexpected data type
-- is found a 'Leaf' With an 'Unknown' 'Role' and error message is
-- created.
unknownTree ∷ (Show a) ⇒
              String     -- ^ Description of the unexpected data type
            → a          -- ^ Unexpected data
            → String     -- ^ Formula name
            → ProofTree  -- ^ 'Unknown' node
unknownTree m r n = Leaf Unknown $ m ++  ' ':show r  ++ " in " ++ n
