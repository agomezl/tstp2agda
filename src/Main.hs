
-- | Main module

{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax       #-}


module Main (main) where


import Options
  (
    Options
    ( optHelp
    , optInputFile
    , optOutputFile
    , optProofName
    , optVersion
    )
    , printUsage
    , processOptions
    )

import           Data.Maybe         (fromMaybe)
import           Data.Proof         (ProofMap, ProofTree)
import           Data.TSTP          (F)
import           System.Environment (getArgs)
import           System.Exit        (exitSuccess)
import           Utils.Functions    (stdout2file)
import           Utils.Monad        (die)
import           Utils.Version      (progNameVersion)

import T2A
  ( buildProofMap
  , buildProofTree
  , getAxioms
  , getConjeture
  , getRefutes
  , getSubGoals
  , parseFile
  , printAuxSignatures
  , printPreamble
  , printProofBody
  , printProofWhere
  , printSubGoals
  )


main ∷ IO ()
main = do
  args ← getArgs
  opts ← case processOptions args of
    Left err → die err
    Right o  → return o

  if  | optHelp opts → printUsage >> exitSuccess

      | optVersion opts → do
        v ← progNameVersion
        putStrLn v  >> exitSuccess

      | otherwise → mainCore opts

-- High level procedure
mainCore ∷ Options → IO ()
mainCore opts = do

  -- Reads all the rules, perhaps more error handling is requiered in
  -- TSTP.hs especially on the alex/happy part of `parseFile` and `parse`
  rules ∷ [F] ← parseFile $ optInputFile opts

  stdout2file $ optOutputFile opts

  -- PREAMBLE : module definitions and imports
  printPreamble

  -- STEP 0 : axioms,conjetures and subgoals
  let subgoals ∷ [F]
      subgoals = getSubGoals rules

  let refutes ∷ [F]
      refutes = getRefutes rules

  let axioms ∷ [F]
      axioms = getAxioms rules

  let conj ∷ F
      conj = fromMaybe
        (error "Couldn't find a conjecture, or it was not unique")
        (getConjeture rules)

  -- Construction of map an tree structures that are meant to be
  -- traversed to create the final Agda code.

  let rulesMap ∷ ProofMap
      rulesMap = buildProofMap rules

  let rulesTrees ∷ [ProofTree]
      rulesTrees = map (buildProofTree rulesMap) refutes

  -- STEP 1 : Print auxiliary functions
  printAuxSignatures rulesMap rulesTrees

  -- STEP 2 : Subgoal handling
  printSubGoals subgoals conj "goals"

  -- STEP 3 : Print main function signature
  printProofBody axioms conj (optProofName opts) subgoals "goals"

  -- STEP 4 :
  mapM_ (printProofWhere rulesMap) rulesTrees
