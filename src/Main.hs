{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Main
-- Author : Alejandro Gómez Londoño
-- Date   : Wed Mar 11 23:29:13 2015
-- Description : Main module for tstp2agda
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------
module Main (main) where

import System.Environment (getArgs)
import Data.TSTP          (Role(Axiom,Conjecture),F,role,name,formula)
import Args               (compileOpts,helpmsg,Flag(..))
import TSTP               (parseFile)
import Data.List          (find,isPrefixOf)
import Data.Maybe         (catMaybes)
import Data.Proof         (buildProofMap,buildProofTree,ProofMap,ProofTree)
import Data.Foldable      (toList)
import System.Exit        (exitFailure)
import T2A.Core           (buildSignature,AgdaSignature(Signature))
import Util               ((▪), unique)

-- Mostly argument handling.
main :: IO ()
main = do
  args <- getArgs
  -- TODO: improve error handling
  case compileOpts args of
   Left [Args.File f] → mainCore f
   Left [Help]   → helpmsg
   Left _        → putStrLn "Bad parameters" >> helpmsg >> exitFailure
   Right e       → putStrLn e >> exitFailure
  return ()


-- High level procedure
mainCore ∷ FilePath → IO ()
mainCore path = do
  -- Reads all the rules, perhaps more error handling is requiered in
  -- TSTP.hs especially on the alex/happy part of `parseFile` and `parse`
  rules  ← parseFile path
  -- STEP 0 : axioms,conjetures and subgoals
  let subgoals = filter (isPrefixOf "subgoal" . name) rules
  let refutes  = filter (isPrefixOf "refute"  . name) rules
  let axioms   =      filter ((==) Axiom      . role) rules
  let conj     = case find   ((==) Conjecture . role) rules of
                   Nothing → error "Couldn't find a conjecture"
                   Just f  → f
  -- Construction of map an tree structures that are meant to be
  -- traversed to create the final Agda code.
  let rulesMap   = buildProofMap rules
  let rulesTrees = map (buildProofTree rulesMap) refutes
  -- STEP 1 : Print auxiliary functions
  mainAuxSignatures rulesMap rulesTrees
  -- STEP 2 : Subgoal handling
  mainSubGoals subgoals conj "goals"
  -- STEP 3 : Print main function signature
  mainBody axioms conj "proof" subgoals "goals"

mainAuxSignatures ∷ ProofMap → [ProofTree] → IO ()
mainAuxSignatures ω γ = mapM_ lineP signatures
    where signatures = unique . concat . map signature $ γ
          signature t = catMaybes -- Remove Nothings
                        . toList  -- Flatten the tree
                                 -- Build (only) the requiered functions
                        . fmap (buildSignature ω) $ t
          lineP s = (putStrLn $ "postulate " ▪ s) >> putStrLn []

mainSubGoals ∷ [F] → F → String → IO ()
mainSubGoals subgoals conj fname = do
  print $ Signature fname $ map formula $ subgoals ++ [conj]
  putStrLn []

mainBody ∷ [F]    -- Axioms
         → F      -- Conjecture
         → String -- Function name
         → [F]    -- Subgoals
         → String -- Subgoals → Conjecture function name
         → IO ()
mainBody axioms conj proofName subgoals goalsName = do
  print $ Signature proofName $ map formula $ axioms ++ [conj]
  putStr $ foldl (▪) proofName (map name axioms)
             ▪ "="
             ▪ foldl (▪) goalsName (map name subgoals)
