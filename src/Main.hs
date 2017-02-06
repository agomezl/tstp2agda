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

import           Data.TSTP            (F (..), Formula (..) )
import           Data.TSTP.Formula    (getFreeVars)
import           Data.TSTP.AtomicWord (AtomicWord (..))
import           Data.TSTP.BinOp      (BinOp (..))
import           Data.TSTP.InfixPred  (InfixPred (..))
import           Data.TSTP.Quant      (Quant (..))
import           Data.TSTP.Term       (Term (..))
import           Data.TSTP.V          (V (..))
import           Utils.Functions      (βshow, (▪), (<>))

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

  let formulas ∷ [Formula]
      formulas = map formula tstp

  case embedding of
    's' → do
      printPreamble embedding 0
      -- STEP 1 : Print auxiliary functions
      printAuxSignatures rulesMap rulesTrees

      -- STEP 2 : Subgoal handling
      printSubGoals subgoals conj "goals"

      -- STEP 3 : Print main function signature
      printProofBody axioms conj (optProofName opts) subgoals "goals"

      -- STEP 4 :
      mapM_ (printProofWhere rulesMap) rulesTrees

    'd' → do

      let freevars ∷ [V]
          freevars = getFreeVars formulas

      printPreamble embedding (length freevars)

      putStrLn "-- Vars"
      printVars freevars 0

      putStrLn "-- Axioms"
      printAxioms axioms

      putStrLn "-- Premises"
      printPremises axioms

      putStrLn "-- Conjecture"
      printConjecture conj

      printProof axioms
      return ()

printVar ∷ V → Int → String
printVar f n = intercalate "\n" $
  [  show f ++ " : Prop"
  ,  show f ++ " = Var (# " ++ show n ++ ")"
  ]

printVars ∷ [V] → Int → IO String
printVars [] _ = return ""
printVars (f : fs) n = do
  putStrLn $ printVar f n ++ "\n"
  printVars fs (n+1)

showDeepFormula ∷ Formula → String
showDeepFormula (BinOp     f₁  (:=>:) f₂) = '(' <> f₁ ▪ '⇒' ▪ f₂ <> ')'
showDeepFormula (BinOp     f₁  op     f₂) = f₁ ▪ op ▪ f₂
showDeepFormula (InfixPred t₁  r      t₂) = t₁ ▪ r  ▪ t₂
showDeepFormula (PredApp   ρ          []) = show ρ
showDeepFormula (PredApp   ρ          φ ) = '(' <> ρ ▪ ':' ▪ φ ▪ "⇒ ⊤" <> ')'
showDeepFormula ((:~:)                f ) = '¬' ▪ f
showDeepFormula _ = "⊤"

printAxiom ∷ F → String
printAxiom f = intercalate "\n" $
  let axiom = name f
  in [  axiom ++ " : Prop"
     ,  axiom ++ " = " ++ showDeepFormula (formula f)
     ]

printAxioms ∷ [F] → IO ()
printAxioms fs = do
  putStrLn "-- Axioms"
  putStrLn $ intercalate "\n\n" $ map printAxiom fs

printPremises ∷ [F] → IO ()
printPremises fs = do
  putStrLn $ "\n-- Premises"
  putStrLn $ "Γ : Ctxt"
  putStrLn $ "Γ = ∅ , " ++ (intercalate " , " (map name fs))

printConjecture ∷ F → IO ()
printConjecture f = do
  putStrLn "\n-- Conjecture"
  putStrLn $ printAxiom f

printProof ∷ [F] → IO ()
printProof _ = do
  putStrLn $ "\n-- Proof"
