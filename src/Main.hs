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

import           Data.TSTP            (F (..), Formula (..), Rule (..), Role (..) )
import           Data.TSTP.Formula    (getFreeVars)
import           Data.TSTP.AtomicWord (AtomicWord (..))
import           Data.TSTP.BinOp      (BinOp (..))
import           Data.TSTP.InfixPred  (InfixPred (..))
import           Data.TSTP.Quant      (Quant (..))
import           Data.TSTP.Term       (Term (..))
import           Data.TSTP.V          (V (..))

import           System.Environment (getArgs)
import           System.Exit        (exitSuccess)
import           Utils.Functions    (βshow, (▪), (<>), stdout2file)
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

debug = True

printVar ∷ V → Int → String
printVar f n = intercalate "\n"
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
showDeepFormula (BinOp f₁ (:=>:) f₂) = '(' <> sf₁ ▪ '⇒' ▪ sf₂ <> ')'
  where
    sf₁, sf₂ ∷ String
    sf₁ = showDeepFormula f₁
    sf₂ = showDeepFormula f₂
showDeepFormula (BinOp f₁ (:<=>:) f₂) = '(' <> sf₁ ▪ '⇔' ▪ sf₂ <> ')'
  where
    sf₁, sf₂ ∷ String
    sf₁ = showDeepFormula f₁
    sf₂ = showDeepFormula f₂

showDeepFormula (BinOp f₁ op f₂) = '(' <> sf₁ ▪ op ▪ sf₂ <> ')'
  where
    sf₁, sf₂ ∷ String
    sf₁ = showDeepFormula f₁
    sf₂ = showDeepFormula f₂
showDeepFormula (InfixPred t₁  r      t₂) = t₁ ▪ r  ▪ t₂
showDeepFormula (PredApp ρ          []) = show ρ
showDeepFormula (PredApp (AtomicWord "$false") []) = "⊥"
showDeepFormula (PredApp (AtomicWord "$true")  []) = "⊤"
showDeepFormula (PredApp ρ          φ ) = '(' <> ρ ▪ ':' ▪ φ ▪ "⇒ ⊤" <> ')'
showDeepFormula ((:~:)              f ) = '¬' ▪ showDeepFormula f
showDeepFormula _ = "RRR"

printAxiom ∷ F → String
printAxiom f =
  let axiom = stdName $ name f
  in concat
    [  axiom ,  " : Prop\n"
    ,  axiom , " = " ,  showDeepFormula (formula f) , "\n"
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
  putStrLn $ "-- Premise" ++ (if length premises < 2 then "" else "s")
  putStrLn "Γ : Ctxt"
  case premises of
    []  → putStrLn "Γ = ∅"
    [p] → putStrLn $ "Γ = [ " ++ name p ++ " ]"
    ps  → putStrLn $ "Γ = ∅ , " ++ intercalate " , " (map name ps)
  putStrLn ""

printConjecture ∷ F → IO ()
printConjecture f = putStrLn $
  concat
    [  "-- Conjecture\n"
    , printAxiom f , "\n"
    ]

printSubGoals' ∷ [F] → IO ()
printSubGoals' [] = return ()
printSubGoals' subgoals = putStrLn $
  concat
    [ "-- Subgoal", if length subgoals < 2 then "" else "s" , "\n"
    , intercalate "\n\n" (map printAxiom subgoals)
    ]

printProof ∷ [F] → [F] → F → ProofMap → [ProofTree] → IO ()
printProof _ _  _ _ [] = return ()
printProof axioms subgoals goal rmap rtree = do
  putStrLn "-- Metis Proof."
  printProofSubgoal 0 axioms subgoals goal rmap rtree
  printProofGoal subgoals goal rmap rtree

printProofSubgoal ∷ Int → [F] → [F] → F → ProofMap → [ProofTree] → IO ()
printProofSubgoal _ _ _ _ _ [] = return ()
printProofSubgoal no axioms subgoals goal rmap (tree:strees) = do
  let strNo       = stdName $ show no
  let proofName   = stdName $ "proof" ++ strNo
  let subgoalName = "subgoal" ++ strNo
  let proof :: String
      proof = concat
        [ proofName , " : Γ ⊢ " , subgoalName , "\n"
        , proofName , " =\n"
        , "  RAA $\n"
        , if debug then ("  -- Γ , ¬ " ++ subgoalName ++ "⊢ ⊥\n") else ""
        , printSteps subgoalName 2 [tree] rmap goal axioms
        ]
  putStrLn proof
  printProofSubgoal (no+1) axioms subgoals goal rmap strees

type Ident = Int

getIdent ∷ Ident → String
getIdent n = concat $ replicate (2 * n) " "


printSteps ∷ String → Ident → [ProofTree] → ProofMap → F → [F] → String
printSteps sname n [Root Negate tag [Root Strip subgoalname st]] dict goal axioms =
  concat
    [ getIdent n , "atp-strip $" , "\n"
    , getIdent (n+1) , "assume {Γ = Γ} $" , "\n"
    , getIdent (n+2) , "atp-neg " , sname , "\n"
    ]

printSteps sname n [Root Simplify tag subtree] dict goal axioms =
  concat
    [ getIdent n , "atp-simplify $\n"
    , getIdent (n+1) , "∧-intro\n"
    , andIntro (n+2) subtree
    ]
    where
--      innerStep ∷ Ident → [ProofTree] → String
      innerStep m step = concat
        [ getIdent m , "(\n"
        , printSteps sname m [step] dict goal axioms
        , getIdent m , ")\n"
        ]

--      andIntro :: Ident → [ProofTree] → String
      andIntro m []       = ""
      andIntro m [x]      = printSteps sname m [x] dict goal axioms
      andIntro m (x:y:[]) = concatMap (innerStep m) [x , y]
      andIntro m (x:xs) = concat
        [ innerStep m x
        , getIdent m , "∧-intro\n"
        , andIntro (m+1) xs
        ]

printSteps sname n [Root inf tag subtree] dict goal axioms =
  concat
    [ getIdent n , inferenceName , " $\n"
    , printSteps sname (n+1) subtree dict goal axioms
    ]
  where
    inferenceName ∷ String
    inferenceName = case inf of
      Canonicalize → "atp-canonicalize"
      Strip        → "atp-strip"
      Conjunct     → "atp-conjunct"
      _            → "? -- inference rule no supported yet"

printSteps sname n [Leaf Conjecture gname] dict goal axioms =
  concat
    [ getIdent n , gname , "\n"
    ]

printSteps sname n [Leaf Axiom gname] dict goal axioms =
  concat
    [ getIdent n , "weaken (atp-neg " , stdName sname , ") $\n"
    , getIdent (n+1) , "(assume {Γ = ∅} " , gname , ")\n"
    ]
printSteps _ n _ _ _ _ = getIdent n ++ "? -- no supported yet\n"

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
stdName nm = map subIndex $ concat $ splitOn "-" nm

andIntroSubgoals :: Ident → Int → [F] → String
andIntroSubgoals m n []       = ""
andIntroSubgoals m n [x]      = getIdent m ++ "subgoal" ++ stdName (show n)
andIntroSubgoals m n (x:y:[]) =
  concat
    [ getIdent m , "subgoal" , stdName (show n) , "\n"
    , getIdent m , "subgoal" , stdName (show (n+1)) , "\n"
    ]
andIntroSubgoals m n (x:xs) =
  concat
    [ getIdent m , "subgoal", stdName (show n) , "\n"
    , getIdent m, "(\n"
    , getIdent m , "∧-intro\n"
    , andIntroSubgoals (m+1) (n+1) xs
    , getIdent m, ")\n"
    ]

printProofGoal :: [F] → F → ProofMap → [ProofTree] → IO ()
printProofGoal [] _ _ _  = putStrLn "-- Proof not available.\n"
printProofGoal [s] _ _ _ = putStrLn $
  concat
    [ "proof : Γ ⊢ goal" , "\n"
    , "proof =" , "\n"
    , getIdent 1 , "⇒-elim", "\n"
    , getIdent 2 , "atp-splitGoal" , "\n"
    , getIdent 2 , "proof₀" , "\n"
    ]

printProofGoal subgoals goal rmap rtree = putStrLn $
  concat
    [ "proof : Γ ⊢ goal" , "\n"
    , "proof =" , "\n"
    , getIdent 1 , "⇒-elim", "\n"
    , getIdent 2 , "atp-splitGoal" , "\n"
    , getIdent 2 , "(\n"
    , getIdent 2 , "∧-intro\n"
    , andIntroSubgoals 3 0 subgoals
    , getIdent 2 , ")\n"
    ]
