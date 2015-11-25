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
import Data.TSTP          (Role(Axiom,Conjecture),F,role,name,formula,bottom)
import Data.TSTP          (Rule(Negate,Strip),getFreeVars)
import Args               (compileOpts,helpmsg,Flag(..))
import TSTP               (parseFile)
import Data.List          (find,isPrefixOf)
import Data.Map as M      (lookup)
import Data.Maybe         (catMaybes, fromMaybe)
import Data.Proof         (buildProofMap,buildProofTree,ProofMap,ProofTree)
import Data.Proof         (ProofTreeGen(..))
import Data.Foldable      (toList)
import Control.Monad      (foldM)
import System.Exit        (exitFailure)
import T2A.Core           (buildSignature)
import T2A.Core           (AgdaSignature(Signature,ScopedSignature))
import Util               ((▪),unique,printInd,putStrLnInd,swapPrefix)

import qualified Data.Foldable as F (find)


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
  -- PREAMBLE : module definitions and imports
  let moduleName = "BaseProof"
  putStrLn $ "module" ▪ moduleName ▪ "where"
  putStrLn $ "open import Data.FOL.Shallow"
  putStrLn []
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
  -- STEP 4 :
  putStrLnInd 2 "where"
  mapM_ (mainWhere rulesMap) rulesTrees

mainAuxSignatures ∷ ProofMap → [ProofTree] → IO ()
mainAuxSignatures ω γ = mapM_ lineP signatures
    where signatures = unique . concat . map signature $ γ
          signature t = catMaybes -- Remove Nothings
                        . toList  -- Flatten the tree
                                 -- Build (only) the requiered functions
                        . fmap (buildSignature ω) $ t
          lineP s = (putStrLn $ "postulate" ▪ s) >> putStrLn []

mainSubGoals ∷ [F] → F → String → IO ()
mainSubGoals subgoals conj fname = do
  putStr "postulate "
  print $ Signature fname $ map formula $ subgoals ++ [conj]
  putStrLn []

mainBody ∷ [F]    -- Axioms
         → F      -- Conjecture
         → String -- Function name
         → [F]    -- Subgoals
         → String -- Subgoals → Conjecture function name
         → IO ()
mainBody axioms conj proofName subgoals goalsName = do
  let f = map formula $ axioms ++ [conj]
  let γ = concat . map (\m → "{" ++ show m ++ "}") $ getFreeVars f
  let ρ = proofName ▪ γ
  print $ Signature proofName $ f
  putStrLn $ foldl (▪) ρ (map name axioms)
             ▪ "="
             ▪ foldl (▪) goalsName (map name subgoals)


mainWhere ∷ ProofMap → ProofTree → IO ()
mainWhere m t = do
  let subgoal = fromMaybe (error "No subgoal") $ F.find (isPrefixOf "subgoal") t
  let negate  = fromMaybe (error "No negate")  $ F.find (isPrefixOf "negate")  t
  (i,a) ← mainWhereBody 4 m t
  putStrLnInd 4 $  subgoal ▪ "=" ▪ "proofByContradiction" ▪ ("fun-" ++ negate)
  return ()

mainWhereBody ∷ Int → ProofMap → ProofTree → IO (Int,String)
mainWhereBody _ _ (Leaf _ a)         = return (4,a)
mainWhereBody ind _ (Root Strip a _) = return (4,a)
mainWhereBody ind m (Root r a p) = do
  let scopeFold (i,a) b = do
        (i₀,a₀) ← mainWhereBody i m b
        return (max i i₀, a ▪ a₀)
  (ξ,ρ) ← foldM scopeFold (ind,"fun-" ++ a) p
  case r of
    Negate → do
           let f = fromMaybe (error "Error formula not found") (M.lookup a m)
           printInd ξ $ ScopedSignature ("fun-" ++ a) [formula f,bottom]
           let negLHS = swapPrefix "negate" "refute" a
           putStrLnInd ξ $ ("fun-" ++ a) ▪ a ▪ "=" ▪ negLHS
           putStrLnInd (ξ + 2) "where"
           return (ξ + 4, a)
    _      → do
           putStrLnInd ξ $ a ▪ "=" ▪ ρ
           return (ξ,a)
