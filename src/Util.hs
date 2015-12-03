{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE CPP #-}
--------------------------------------------------------------------------------
-- File   : Util
-- Author : Alejandro Gomez
-- Date   : Tue Oct 27 13:18:40 2015
-- Description :
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------
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
            ) where

import Data.Foldable      (toList)
import Data.Set           (fromList)
import Data.List          (isPrefixOf)
import System.IO          (IOMode(WriteMode),openFile,stdout)
import GHC.IO.Handle      (hDuplicateTo)

infixr 4 ▪

-- | '"foo" ▪ "bar"' = '"foo bar"'. its main use is to simplify the
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

-- | Metis identifiers usually contain '_' characters which are invalid
-- in Agda, 'agdafy' replaces @normalize_0_0@ with
-- @normalize-0-0@. This is mostly used inside the Happy parser every
-- time an 'AtomicWord' is created.
agdafy ∷ String → String
agdafy = map repl
    where repl '_' = '-'
          repl  a  = a

stdout2file ∷ Maybe FilePath → IO ()
stdout2file Nothing  = return ()
stdout2file (Just o) = openFile o WriteMode >>= flip hDuplicateTo stdout
