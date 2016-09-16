
-- | Util module

{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE UnicodeSyntax             #-}

#ifndef MIN_VERSION_base
#define MIN_VERSION_base(a,b,c) 1
#endif

-- Assume we are using the newest versions when using ghci without cabal
module Util (
  -- * Spaced concatenation
    (▪)
  , BShow(..)
  -- * Printing with indentation
  , printInd
  , putStrLnInd
  -- * List manipulation
  , unique
  , swapPrefix
  -- * Others
  , agdafy
  , stdout2file
  , checkIdScope
  ) where

import           Data.Foldable (toList)
import           Data.List     (isPrefixOf)
import           Data.Set      (Set, fromList)
import           GHC.IO.Handle (hDuplicateTo)
import           System.IO     (IOMode (WriteMode), openFile, stdout)
#if MIN_VERSION_base(4,7,0)
import           Data.Foldable (any)
import           Prelude       hiding (any)
#endif

infixr 4 ▪

-- | '"foo" ▪ "bar"' = '"foo bar"'. Its main use is to simplify the
-- concatenation of printable types separated by spaces.
(▪) ∷ forall a b. (BShow a, BShow b) ⇒ a → b → String
(▪) α₁ α₂ = βshow α₁ ++ " " ++ βshow α₂

-- | 'BShow' fixes 'Show' 'String' instance behavior @length "foo" ≠
-- length (show "foo")@ with two new instances (and overlapped)
-- instances for 'String' and 'Show' 'a'.

class BShow a where
    βshow ∷ a -> String

-- TODO: fix overlapping mess

#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPING #-} BShow String where
#else
instance BShow String where
#endif
    βshow a = a

#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPING #-} BShow Char where
#else
instance BShow Char where
#endif
    βshow a = [a]

#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPABLE #-} Show a ⇒ BShow a where
#else
instance Show a ⇒ BShow a where
#endif
  βshow = show

-- | Removes duplicate elements of a list.
unique ∷ (Ord a) ⇒ [a] → [a]
unique a = toList . fromList $ a

-- | 'printInd' @i b@, prints a with @b@ level of indentation @i@.
printInd ∷ (Show a) ⇒ Int → a → IO ()
printInd ind a = putStr spaces >> print a
    where spaces = replicate ind ' '

-- | 'printInd' @i str@, prints a with @str@ level of indentation @i@.
putStrLnInd ∷ Int → String → IO ()
putStrLnInd ind a = putStr spaces >> putStrLn a
    where spaces = replicate ind ' '


-- | 'swapPrefix' @a b str@, replaces prefix @a@ in @str@ with @b@
-- checking that @a@ is a prefix of @str@.
swapPrefix ∷ Eq a ⇒
             [a] -- ^ Current prefix
           → [a] -- ^ Replacement
           → [a] -- ^ List to be replaced
           → [a] -- ^ Resulting list
swapPrefix a b str
    | a `isPrefixOf`str = b ++ drop (length a) str
    | otherwise         = str

-- | <http://www.gilith.com/software/metis/ Metis>
-- identifiers usually contain @_@ characters which are invalid in
-- <http://wiki.portal.chalmers.se/agda/pmwiki.php Agda>, 'agdafy'
-- replaces @normalize_0_0@ with @normalize-0-0@.  This is
-- mostly used inside the
-- <https://www.haskell.org/happy/ Happy>
-- parser every time an 'Data.TSTP.AtomicWord' is created.
agdafy ∷ String → String
agdafy = map repl
    where repl '_' = '-'
          repl  a  = a

-- | Redirect all stdout output into a file or do nothing (in case of
-- 'Nothing')
stdout2file ∷ Maybe FilePath → IO ()
stdout2file Nothing  = return ()
stdout2file (Just o) = openFile o WriteMode >>= flip hDuplicateTo stdout

-- | 'checkIdScope' @i t s@ check if any name in @s@ has a more
-- general scope than @t@ with level @i@
checkIdScope ∷ Int → String → Set (Int,String) → Bool
checkIdScope i f s = any (\(i₀,f₀) →  f₀ == f && i₀ <= i ) s
