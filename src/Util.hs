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

infixr 4 ▪

(▪) ∷ forall a b. (BShow a, BShow b) ⇒ a → b → String
(▪) α₁ α₂ = βshow α₁ ++ " " ++ βshow α₂

class BShow a where
    βshow ∷ a -> String

instance BShow String where
    βshow a = a

instance BShow Char where
    βshow a = [a]

#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPABLE #-} Show a ⇒ BShow a where
#else
instance Show a ⇒ BShow a where
#endif
  βshow = show
