
-- | Tactics

{-# LANGUAGE UnicodeSyntax #-}

module T2A.Tactics
  ( -- * Types
    Tactic
    -- * Solvers
  , resolveTactic
  , resolveTacticGen
  -- * Tactics
  , identity
  ) where

import           Data.Maybe (mapMaybe)
import           Data.TSTP  (Formula (..))
import           T2A.Core   (AgdaSignature (Signature))
import           Util       ((▪))

-- | A 'Tactic' is a function that tries to give a corresponding
-- implementation to a Metis-generated proof step:
--
-- Given some Metis-generated Formulae
--
-- @
-- fof(a1, axiom, (a)).
--
-- fof(normalize_0_2, plain, (a), inference(canonicalize, [], [a1])).
-- @
--
-- @tstp2agda@ will generate the following signature for the function
-- @fun-normalize-0-2@ that given @a1@ return @normalize_0_2@
-- (Actually their corresponding formula)
--
-- @
-- fun-normalize-0-2 : {a : Set} → a → a
-- @
--
-- A 'Tactic' is function that given a signature in the form of
-- 'AgdaSignature' will determine the corresponding "implementation"
--
-- @
-- fun-normalize-0-2 : { a : Set} → a → a
-- fun-normalize-0-2 = id
-- @
--
type Tactic = AgdaSignature → Maybe (IO ())

-- | 'resolveTactic' @τ@ @χ@ tries to find and implementation for @τ@
-- using every tactic in @χ@ and in case of failure prints the default
-- implementation.
resolveTactic ∷ AgdaSignature → [Tactic] → IO ()
resolveTactic τ γ = case mapMaybe (flip ($) τ) γ of
                      [] → asPostulate τ
                      (x:xs) → do otherOptions xs
                                  x
    where otherOptions x = putStrLn $ "--" ▪ length x ▪ "more viable options"


-- | Default implementation for any 'AgdaSignature' as an Agda postulate.
asPostulate ∷ AgdaSignature → IO ()
asPostulate s = (putStrLn $ "postulate" ▪ s) >> putStrLn []

-- | In Metis some applications of the inference rule @canonicalize@
-- result in trivial [a ↦ a] behavior that is captured in Agda with the
-- identity function.
identity ∷ Tactic
identity τ@(Signature n [x1,x2])
    | x1 == x2  = Just $ do print τ
                            putStrLn $ n ▪ "= id"
                            putStrLn []
    | otherwise = Nothing
identity _      = Nothing

-- | Similar to 'resolveTactic' but using all the build-in tactics.
resolveTacticGen ∷ AgdaSignature →  IO ()
resolveTacticGen τ = resolveTactic τ tacList
    where tacList = [identity]
