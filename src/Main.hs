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
import Args               (compileOpts,helpmsg,Flag(..),Conf(..))
import Data.Maybe         (isNothing)

import System.Exit        (exitFailure,exitSuccess)
import System.IO          (getContents,IOMode(WriteMode),openFile,stdout)
import GHC.IO.Handle      (hDuplicateTo)
import Util               ((▪),unique,printInd,putStrLnInd,swapPrefix)

import T2A (buildProofMap,buildProofTree,parseFile)
import T2A (getSubGoals,getAxioms,getRefutes,getConjeture,printPreamble)
import T2A (printAuxSignatures,printSubGoals,printProofBody,printProofWhere)

import qualified Data.Foldable as F (find)


-- Mostly argument handling.
main :: IO ()
main = do
  args <- getArgs
  -- TODO: improve error handling
  -- TODO: make prettier
  mainCore =<< case compileOpts args of
                 -- Something went wrong whit the flags
                 Right e                → putStrLn e >> exitFailure
                 -- Help message display
                 Left (Conf _  _ True)  → helpmsg    >> exitSuccess
                 -- Input and Output file selection
                 Left (Conf f (Nothing) _) → return f
                 Left (Conf f (Just o ) _) → do hnd ← openFile o WriteMode
                                                hDuplicateTo hnd stdout
                                                return f
-- High level procedure
mainCore ∷ Maybe FilePath → IO ()
mainCore path = do
  -- Reads all the rules, perhaps more error handling is requiered in
  -- TSTP.hs especially on the alex/happy part of `parseFile` and `parse`
  rules  ← parseFile path
  -- PREAMBLE : module definitions and imports
  printPreamble "BaseProof"
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
  printProofBody axioms conj "proof" subgoals "goals"
  -- STEP 4 :
  mapM_ (printProofWhere rulesMap) rulesTrees
