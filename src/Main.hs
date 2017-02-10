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

import Data.List
import Data.List.Split


import           Data.Maybe         (fromJust, fromMaybe)
import           Data.Proof         (ProofMap, ProofTree)

import           Data.TSTP            (F (..), Formula (..), Rule (..), Role (..) )
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

import Data.Proof (ProofTree (..), ProofMap (..), ProofTreeGen(..) )

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

      printAxioms axioms

      printPremises axioms

      printConjecture conj


      printSubGoals' subgoals


      printProof axioms subgoals conj rulesMap rulesTrees
      return ()

printVar ∷ V → Int → String
printVar f n = intercalate "\n" $
  [  show f ++ " : Prop"
  ,  show f ++ case show f of
       "$true" → " = ⊤"
       "$false"→ " = ⊥"
       s → " = Var (# " ++ show n ++ ")"
  ]

printVars ∷ [V] → Int → IO String
printVars [] _ = return ""
printVars (f : fs) n = do
  putStrLn $ printVar f n ++ "\n"
  printVars fs (n+1)

showDeepFormula ∷ Formula → String
showDeepFormula (BinOp     f₁  (:=>:) f₂) = '(' <> sf₁ ▪ '⇒' ▪ sf₂ <> ')'
  where
    sf₁ = showDeepFormula f₁
    sf₂ = showDeepFormula f₂
showDeepFormula (BinOp     f₁  (:<=>:) f₂) = '(' <> sf₁ ▪ '⇔' ▪ sf₂ <> ')'
  where
    sf₁ = showDeepFormula f₁
    sf₂ = showDeepFormula f₂

showDeepFormula (BinOp     f₁  op     f₂) = '(' <> sf₁ ▪ op ▪ sf₂ <> ')'
  where
    sf₁ = showDeepFormula f₁
    sf₂ = showDeepFormula f₂
showDeepFormula (InfixPred t₁  r      t₂) = t₁ ▪ r  ▪ t₂
showDeepFormula (PredApp   ρ          []) = show ρ
showDeepFormula (PredApp   (AtomicWord "$false")          []) = "⊥"
showDeepFormula (PredApp   (AtomicWord "$true")          []) = "⊤"
showDeepFormula (PredApp   ρ          []) = show ρ

showDeepFormula (PredApp   ρ          φ ) = '(' <> ρ ▪ ':' ▪ φ ▪ "⇒ ⊤" <> ')'

showDeepFormula ((:~:)                f ) = '¬' ▪ (showDeepFormula f)
showDeepFormula _ = "RRR"

printAxiom ∷ F → String
printAxiom f = intercalate "\n" $
  let axiom = stdName (name f)
  in [  axiom ++ " : Prop"
     ,  axiom ++ " = " ++ showDeepFormula (formula f)
     ]

printAxioms ∷ [F] → IO ()
printAxioms [] = return ()
printAxioms [a] = do
  putStrLn "-- Axiom"
  putStrLn $ printAxiom a ++ "\n"
printAxioms as = do
  putStrLn "-- Axioms"
  putStrLn $ intercalate "\n\n" $ map printAxiom as
  putStrLn ""

printPremises ∷ [F] → IO ()
printPremises premises = do
  putStrLn $ "-- Premise" ++ (if (length premises < 2) then "" else "s")
  putStrLn "Γ : Ctxt"
  case premises of
    []  → putStrLn "Γ = ∅"
    [p] → putStrLn $ "Γ = [ " ++ name p ++ " ]\n"
    ps  → putStrLn $ "Γ = ∅ , " ++ (intercalate " , " (map name ps))
  putStrLn ""

printConjecture ∷ F → IO ()
printConjecture f = do
  putStrLn "-- Conjecture"
  putStrLn $ printAxiom f ++ "\n"

printSubGoals' ∷ [F] → IO ()
printSubGoals' [] = return ()
printSubGoals' subgoals = do
  putStrLn $ "-- Subgoal"++ if length subgoals < 2 then "" else "s"
  putStrLn $ intercalate "\n\n" $ map printAxiom subgoals
  putStrLn ""

printProof ∷ [F] → [F] → F → ProofMap → [ProofTree] → IO ()
printProof _      _        _    _    [] = return ()
printProof axioms subgoals goal rmap rtree = do
  putStrLn "-- Metis Proof."
  printProofSubgoal 0 axioms subgoals goal rmap rtree

printProofSubgoal ∷ Int → [F] → [F] → F → ProofMap → [ProofTree] → IO ()
printProofSubgoal _ _ _ _ _ [] = return ()
printProofSubgoal no axioms subgoals goal rmap (tree:strees) = do
  let strNo = stdName (show no)
  let proofName = stdName ( "proof" ++ strNo)
  let subgoalName = "subgoal" ++ strNo
  putStrLn $ proofName ++ " : Γ ⊢ " ++ subgoalName
  putStrLn $ proofName ++ " ="
  putStrLn "  RAA $"
  putStrLn $ printSteps subgoalName 2 [tree] rmap goal axioms
  putStrLn "\n"
  printProofSubgoal (no+1) axioms subgoals goal rmap strees

type Ident = Int

getIdent ∷ Ident → String
getIdent n = concat $ replicate (2 * n) " "

printSteps ∷ String → Ident → [ProofTree] → ProofMap → F → [F] → String
printSteps sname n [(Root Negate tag [(Root Strip subgoalname st)] )] dict goal axioms =
  if sname == (stdName subgoalname) then
    getIdent n ++ "atp-strip $\n" ++ getIdent (n+1) ++ "assume {Γ = Γ} $\n" ++ getIdent (n+2) ++ "atp-neg " ++ sname
  else do
    getIdent n ++ "atp-negate $" ++ printSteps sname (n+1) [(Root Strip subgoalname st)] dict goal axioms

printSteps sname n [(Root inf tag subtree)] dict goal axioms =
  getIdent n ++ inferenceName ++ " $\n" ++ printSteps sname (n+1) subtree dict goal axioms
  where
    inferenceName ∷ String
    inferenceName = case inf of
      Canonicalize → "atp-canonicalize"
      Strip  → "atp-strip"
      _ → "inference rule no supported yet"

printSteps sname n [Leaf Conjecture gname] dict goal axioms =
  getIdent n ++ gname ++ "\n"
printSteps _ _ _ _ _ _ = "-- no supported yet"


subIndex ∷ Char → Char
subIndex '0' = '₀'
subIndex '1' = '₁'
subIndex '2' = '₂'
subIndex '3' = '₃'
subIndex '4' = '₄'
subIndex '5' = '₅'
subIndex '6' = '₆'
subIndex '7' = '₇'
subIndex '8' = '₈'
subIndex '9' = '₉'
subIndex s   = s

stdName :: String → String
stdName name = map subIndex $ concat $ splitOn "-" name
