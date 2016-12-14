
-- | Main module

{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax       #-}


module Main (main) where


import Options
  (
    Options
    ( optEmbedding
    , optHelp
    , optInputFile
    , optOutputFile
    , optProofName
    , optVersion
    )
    , printUsage
    , processOptions
    )

import Data.List (intercalate)


import           Data.Maybe         (fromJust, fromMaybe)
import           Data.Proof         (ProofMap, ProofTree)
import           Data.TSTP          (F (..), Formula (..) )
import           System.Environment (getArgs)
import           System.Exit        (exitSuccess)
import           Utils.Functions    (stdout2file)
import           Utils.Monad        (die)
import           Utils.PrettyPrint  (text)
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

      | otherwise → do
          file ← case optInputFile opts of
            Nothing → die $ text "missing input file (try --help)"
            Just f  → return f
          mainCore opts

-- High level procedure
mainCore ∷ Options → IO ()
mainCore opts = do

  tstp ∷ [F] ← parseFile $ fromJust $ optInputFile opts


  -- STEP 0 : axioms,conjetures and subgoals
  let subgoals ∷ [F]
      subgoals = getSubGoals tstp

  let refutes ∷ [F]
      refutes = getRefutes tstp

  let axioms ∷ [F]
      axioms = getAxioms tstp

  let conj ∷ F
      conj = fromMaybe
        (error "Couldn't find a conjecture, or it was not unique")
        (getConjeture tstp)

  -- Construction of map and tree structures that are meant to be
  -- traversed to create the final Agda code.

  let rulesMap ∷ ProofMap
      rulesMap = buildProofMap tstp

  let rulesTrees ∷ [ProofTree]
      rulesTrees = map (buildProofTree rulesMap) refutes

  let embedding ∷ Char
      embedding = optEmbedding opts

  stdout2file $ optOutputFile opts
  printPreamble embedding (length axioms)

  case embedding of
    's' → do
      -- STEP 1 : Print auxiliary functions
      printAuxSignatures rulesMap rulesTrees

      -- STEP 2 : Subgoal handling
      printSubGoals subgoals conj "goals"

      -- STEP 3 : Print main function signature
      printProofBody axioms conj (optProofName opts) subgoals "goals"

      -- STEP 4 :
      mapM_ (printProofWhere rulesMap) rulesTrees

    'd' → do
      putStrLn "-- Definitions "
      printAxioms axioms
      return ()


printDeepFormula ∷ Formula → String
printDeepFormula f = "⊤"


printAxiom :: F → String
printAxiom f = intercalate "\n" $
  let axiom = name f
  in [  axiom ++ " : " ++ "Prop"
     ,  axiom ++ " = " ++ printDeepFormula (formula f)
     ]

printAxioms :: [F] → IO ()
printAxioms fs = putStrLn $
  intercalate "\n\n" $ map printAxiom fs
