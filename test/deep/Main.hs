
-- TODO: take a line in tptp format and parse it
-- TODO: take and axiom and print it
-- TODO: check the formula, the info, the annotation
-- TODO: if it is an axiom and nothing more, prove it
-- and generate the agda code using deep.
-- TODO: to prove in agda, use repeatly weaken..

{-# LANGUAGE UnicodeSyntax #-}

import TSTP ( parse )

import Data.TSTP ( F(..) )
import Data.TSTP.Role       ( Role (..) )

import T2A
  (
   buildProofMap
  , buildProofTree
  , getAxioms
  , getSubGoals
  , getConjeture
  , getRefutes
  -- , getSubGoals
  -- , parseFile
  -- , printAuxSignatures
  -- , printPreamble
  -- , printProofBody
  -- , printProofWhere
  -- , printSubGoals
  )

import Data.Proof (ProofMap, ProofTree)


import qualified Text.Show.Pretty as Pr
import Data.Maybe
import Data.List


isConjecture :: F → [F] → Bool
isConjecture _ [] = False
isConjecture goal (f:fs)
  | formula goal == formula f = True
  | otherwise                 = isConjecture goal fs

prop n ="/home/hotel/tstp2agda/test/problems/prop-" ++ num ++ ".tstp"
  where
    num = if n < 9
      then "00" ++ show n
      else "0" ++ show n

problem n = parse <$> readFile (prop n)


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


main ∷ IO ()
main = do
  return ()

info :: Int -> IO ()
info n = do

  tstp <-  problem n
  putStrLn $ Pr.ppShow tstp
  putStrLn $ "role: " ++ stepAgda (head tstp)

  let axioms ∷ [F]
      axioms = getAxioms tstp
  putStrLn $ Pr.ppShow axioms

  let conjecture ∷ Maybe F
      conjecture = getConjeture tstp

  putStrLn "Conjecture"
  putStrLn $ Pr.ppShow conjecture
  putStrLn ""

  putStrLn "Subgoals"
  putStrLn $ Pr.ppShow (getSubGoals tstp)
  putStrLn ""

  let test1 = isConjecture (fromJust conjecture) axioms
  if test1
    then do
      putStrLn "weaken  = axioms phi"
    else do
      putStrLn "asdf"

  let refutes ∷ [F]
      refutes = getRefutes tstp

  putStrLn "Refutes"
  putStrLn $ Pr.ppShow refutes

  let rulesMap ∷ ProofMap
      rulesMap = buildProofMap tstp

  putStrLn "ProofMap"
  putStrLn $ Pr.ppShow rulesMap

  let rulesTrees ∷ [ProofTree]
      rulesTrees = map (buildProofTree rulesMap) refutes

  putStrLn $ "ProofTree"
  putStrLn $ Pr.ppShow rulesTrees

  
  return ()

type AgdaCode = String

stepAgda :: F → AgdaCode
stepAgda formula =
  case role formula of
    Axiom       → "axioma!!"
    Conjecture  → "no se sabe"

