
-- | Data.Proof module

{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE CPP #-}


#ifndef MIN_VERSION_base
#define MIN_VERSION_base(a,b,c) 1
#endif
-- Assume we are using the newest versions when using ghci without cabal

module Data.Proof
  ( -- * Types
    ProofTreeGen(..)
  , ProofTree
  , ProofMap
  , IdSet
  -- * Constructors
  , buildProofTree
  , buildProofMap
  -- * Internals
  , getParents
  , getParentsTree
  , unknownTree
  ) where

import Data.Map                 (Map, empty, insert)
import Data.Map as M            (lookup)
import Data.Maybe               (catMaybes)
import Data.TSTP                (Formula(..),F(..),Parent(..),Source(..))
import qualified Data.TSTP as R (Role(..),Rule(..))
import Data.Set                 (Set)
#if MIN_VERSION_base(4,7,0)
import Prelude hiding           (foldr,foldl)
import Control.Applicative      ((<$>),(<*>))
import Data.Foldable            (Foldable(..))
import Data.Traversable         (Traversable(..))
#endif

-- | Generic tree structure for representing the structure of a proof.
data ProofTreeGen a =
    -- | 'Leaf' 'r' 'a' is a node with 'R.Role' 'r' and content 'a' (usually
    -- 'String', 'F' or 'Formula') and with no dependencies in other nodes.
    Leaf R.Role a |
    -- | 'Root' 'r' 'a' 'd' is a node with deduction 'R.Rule' 'r', content 'a'
    -- (usually 'String', 'F' or 'Formula'),  and dependencies 'd'.
    Root R.Rule a [ProofTreeGen a]
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
    foldr f b (Leaf r a)    = f a b
    foldr f b (Root r a t)  = f a $ foldr (flip $ foldr f) b t

instance Traversable ProofTreeGen where
    traverse f (Leaf r a)    = Leaf r <$> f a
    traverse f (Root r a t)  = Root r <$> f a <*> traverse (traverse f) t

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
buildProofTree _ (F n R.Axiom _ _)      = Leaf R.Axiom n
buildProofTree _ (F n R.Conjecture _ _) = Leaf R.Conjecture n
buildProofTree m (F n R.Plain _ s)      = caseSrc s
    where caseSrc  (Inference r _ p) = let parents = getParentsTree m p
                                       in Root r n parents
          caseSrc  _                 = unknownMsg
          unknownMsg                 = unknownTree "Source" s n
buildProofTree _ (F n r       _ _)      = unknownTree "Role" r n

-- | 'buildProofMap' 'lf', given a list of functions 'lf' builds a 'ProofMap'
buildProofMap ∷ [F]      -- ^ List of functions
              → ProofMap -- ^ Map of the given functions indexed by its names
buildProofMap f = foldl buildMap empty f
    where buildMap m f' = insert (name f') f' m

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
getParents ω ρ = catMaybes $ map (flip M.lookup $ ω) parents
    where parents  = map (\(Parent s _) → s) ρ

-- | When an unknown 'R.Rule', 'Source', or other unexpected data type
-- is found a 'Leaf' With an 'R.Unknown' 'R.Role' and error message is
-- created.
unknownTree ∷ (Show a) ⇒
              String     -- ^ Description of the unexpected data type
            → a          -- ^ Unexpected data
            → String     -- ^ Formula name
            → ProofTree  -- ^ 'R.Unknown' node
unknownTree m r n = Leaf R.Unknown $ m ++  ' ':show r  ++ " in " ++ n
