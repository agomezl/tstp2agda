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
import Data.Map as M (lookup)
import Data.Proof (ProofMap,getParents)
import Util ((▪))

-- Single function signature
data AgdaSignature = Signature {
      fname ∷ String,
      fcore ∷ [Formula]
    }

-- Given a proof map (ω) and some formula name (φ), construct
-- the appropriated `AgdaSignature`
buildSignature ∷ ProofMap → String → Maybe AgdaSignature
buildSignature ω φ = do
  φ' ← M.lookup φ ω
  let ζ = formula φ'
  let ρ = case source φ' of
            Inference _ _ ρ' → map formula $ getParents ω ρ'
            _                → []
  return $ Signature φ (ρ ++ [ζ])


-- Pretty prints an `AgdaSignature`
printAgda ∷ AgdaSignature → IO ()
printAgda (Signature α ρ) = do
  putStr $ α ▪ " : "
  putStrLn $ show ρ
