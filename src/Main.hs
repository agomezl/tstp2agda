
-- | Main module

{-# LANGUAGE UnicodeSyntax #-}

module Main (main) where

import Args
  ( Conf (..)
  , compileOpts
  , Flag (..)
  , helpmsg
  )

import qualified Data.Foldable      as F (find)
import           Data.Maybe         (isNothing)
import           System.Environment (getArgs)
import           System.Exit        (exitFailure, exitSuccess)
import           System.IO          (getContents)

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

import Util
  ( printInd
  , putStrLnInd
  , stdout2file
  , swapPrefix
  , unique
  , (▪)
  )


main ∷ IO ()
main = do
  args ← getArgs
  -- TODO: improve error handling
  -- TODO: make prettier
  opts ← case compileOpts args of
     -- Something went wrong whit the flags
     Right e                   → putStrLn e >> exitFailure
     -- Help message display
     Left (Conf _  _ True _ _) → helpmsg    >> exitSuccess
     -- Return configuration data type
     Left conf                 → return conf

  mainCore opts

-- High level procedure
mainCore ∷ Conf → IO ()
mainCore (Conf path opath _ moduleN proofN) = do
  -- Reads all the rules, perhaps more error handling is requiered in
  -- TSTP.hs especially on the alex/happy part of `parseFile` and `parse`
  rules ← parseFile path
  stdout2file opath
  -- PREAMBLE : module definitions and imports
  printPreamble moduleN
  -- STEP 0 : axioms,conjetures and subgoals
  let subgoals = getSubGoals rules
  let refutes  = getRefutes rules
  let axioms   = getAxioms rules
  let conj     = case getConjeture rules of
                   Nothing → error "Couldn't find a conjecture, or it was not unique"
                   Just f  → f
  -- Construction of map an tree structures that are meant to be
  -- traversed to create the final Agda code.
  let rulesMap   = buildProofMap rules
  let rulesTrees = map (buildProofTree rulesMap) refutes
  -- STEP 1 : Print auxiliary functions
  printAuxSignatures rulesMap rulesTrees
  -- STEP 2 : Subgoal handling
  printSubGoals subgoals conj "goals"
  -- STEP 3 : Print main function signature
  printProofBody axioms conj proofN subgoals "goals"
  -- STEP 4 :
  mapM_ (printProofWhere rulesMap) rulesTrees
