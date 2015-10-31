{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
--------------------------------------------------------------------------------
-- File   : Util
-- Author : Alejandro Gomez
-- Date   : Tue Oct 27 13:18:40 2015
-- Description :
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------

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

instance {-# OVERLAPPABLE #-} Show a ⇒ BShow a where
    βshow = show
