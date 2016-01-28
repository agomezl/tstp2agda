{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Tactics
-- Author : Alejandro Gómez-Londoño
-- Date   : Wed Jan 27 23:29:12 2016
-- Description :
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------
module T2A.Tactics (
                    resolveTacticGen
                   ) where

import Data.TSTP  (Formula(..))
import Data.Maybe (mapMaybe)
import T2A.Core   (AgdaSignature(Signature))
import Util               ((▪))

type Tactic = AgdaSignature → Maybe (IO ())

resolveTactic ∷ AgdaSignature → [Tactic] → IO ()
resolveTactic τ γ = case mapMaybe (flip ($) τ) γ of
                      [] → asPostulate τ
                      (x:xs) → do otherOptions xs
                                  x
    where otherOptions x = putStrLn $ "--" ▪ length x ▪ "more viable options"

asPostulate ∷ AgdaSignature → IO ()
asPostulate s = (putStrLn $ "postulate" ▪ s) >> putStrLn []

identity ∷ Tactic
identity τ@(Signature n [x1,x2])
    | x1 == x2  = Just $ do print τ
                            putStrLn $ n ▪ "= id"
                            putStrLn []
    | otherwise = Nothing
identity _      = Nothing

resolveTacticGen ∷ AgdaSignature →  IO ()
resolveTacticGen τ = resolveTactic τ tacList
    where tacList = [identity]
