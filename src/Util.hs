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
module Util where

import Data.Foldable      (toList)
import Data.Set           (fromList)
import Data.List          (isPrefixOf)

infixr 4 ▪

(▪) ∷ forall a b. (BShow a, BShow b) ⇒ a → b → String
(▪) α₁ α₂ = βshow α₁ ++ " " ++ βshow α₂

class BShow a where
    βshow ∷ a -> String

instance {-# OVERLAPPING #-} BShow String where
    βshow a = a

instance {-# OVERLAPPING #-} BShow Char where
    βshow a = [a]

#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPABLE #-} Show a ⇒ BShow a where
#else
instance Show a ⇒ BShow a where
#endif
  βshow = show

unique ∷ (Ord a) ⇒ [a] → [a]
unique a = toList . fromList $ a

printInd ∷ (Show a) ⇒ Int → a → IO ()
printInd ind a = putStr spaces >> print a
    where spaces = replicate ind ' '

putStrLnInd ∷ Int → String → IO ()
putStrLnInd ind a = putStr spaces >> putStrLn a
    where spaces = replicate ind ' '


swapPrefix ∷ String → String → String → String
swapPrefix a b str
    | a `isPrefixOf`str = b ++ drop (length a) str
    | otherwise         = str

agdafy ∷ String → String
agdafy = map repl
    where repl '_' = '-'
          repl  a  = a
