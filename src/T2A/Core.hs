{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Core
-- Author : Alejandro Gómez-Londoño
-- Date   : Wed Oct  7 23:30:16 2015
-- Description : Core module of tstp2agda
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------

module T2A.Core where

import Data.TSTP (F(..),Formula(..),Source(..),Role(..))



data AgdaSignature = Signature {
      fname ∷ String,
      fcore ∷ Formula
    }

printAgda ∷ AgdaSignature → IO ()
printAgda (Signature α ρ) = do
  putStr α >> putStr " : "
  putStrLn $ show ρ
