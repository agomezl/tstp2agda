
-- | T2A module

{-# OPTIONS -fno-warn-missing-signatures  #-}

{-# LANGUAGE UnicodeSyntax                #-}


module T2A (
   -- * Getters
     getSubGoals
   , getAxioms
   , getConjeture
   , getRefutes
   -- * Agda translation
   , buildProofMap
   , buildProofTree
   , printAuxSignatures
   , printPreamble
   , printProofBody
   , printProofWhere
   , printSubGoals
   -- * TSTP parsing
   , parseFile
   ) where


import           Control.Monad (foldM)
import           Data.Foldable (toList)
import qualified Data.Foldable as F (find)
import           Data.List     (isPrefixOf)
import           Data.Map      as M (lookup)
import           Data.Maybe    (catMaybes, fromMaybe)

import Data.Proof
  ( buildProofMap
  , buildProofTree
  , IdSet
  , ProofMap
  , ProofTree
  , ProofTreeGen (..)
  )

import           Data.Set      as S (empty, insert, union)

import Data.TSTP
  ( bottom
  , F (formula, name, role)
  , Formula
  , getFreeVars
  , Role (Axiom, Conjecture)
  , Rule (Negate, Strip)
  )

import T2A.Core
  ( AgdaSignature (ScopedSignature, Signature)
  , buildSignature
  )

import           T2A.Tactics   (resolveTacticGen)
import           TSTP          (parseFile)
import Utils.Functions
  ( (▪)
  , checkIdScope
  , printInd
  , putStrLnInd
  , swapPrefix
  , unique
  )


-- | Extract subgoals from a list of formulae.
getSubGoals ∷ [F] → [F]
getSubGoals = filter (isPrefixOf "subgoal" . name)

-- | Extract refuting steps from a list of formulae.
getRefutes ∷ [F] → [F]
getRefutes = filter (isPrefixOf "refute"  . name)

-- | Extract axioms from a list of formulae.
getAxioms ∷ [F] → [F]
getAxioms = filter ((==) Axiom . role)

-- | Try to extract a conjecture from a list of formulae and checks
-- for uniqueness.
getConjeture ∷ [F] → Maybe F
getConjeture rules =
  case filter ((==) Conjecture . role) rules of
    [l] → Just l
    _   → Nothing

printPreamble ∷ IO ()
printPreamble = do
  putStrLn $ "\n-- | tstp2agda proof\n"
  putStrLn "open import Data.FOL.Shallow"
  putStrLn "open import Function using (id)\n"

-- | Print a series of auxiliary functions required to perform most
-- of the steps of the proof. Every 'Data.TSTP.Formula' has a corresponding
-- function which has its parents as arguments and the current
-- function as return value. Since a proof is split in various
-- subgoals, this function receives a list of sub-'ProofTree's
--
-- @
--    fun-stepₘ_ₙ : { ν₀ ... νᵢ : Set } → stepₘ_ₙ₁ → ... → stepₘ_ₙⱼ → stepₘ_ₙ
-- @
printAuxSignatures ∷ ProofMap    -- ^ map of formulas
                   → [ProofTree] -- ^ list of subgoals
                   → IO ()
printAuxSignatures ω γ = mapM_ resolveTacticGen signatures
  where
    signatures ∷ [AgdaSignature]
    signatures = unique . concatMap signature $ γ

    signature ∷ ProofTree → [AgdaSignature]
    signature = catMaybes -- Remove Nothings
                . toList  -- Flatten the tree
                          -- Build (only) the required functions
                . fmap (buildSignature ω)

-- | Print the main subgoal implication function
--
-- @
--   subGoalImplName : subgoal₀ → ... → subgoalₙ → conjecture
-- @
printSubGoals ∷ [F]     -- ^ Subgoals
              → F       -- ^ Conjecture
              → String  -- ^ Function name (@subGoalImplName@)
              → IO ()
printSubGoals subgoals conj fname = do
  putStr "postulate "
  print $ Signature fname $ map formula $ subgoals ++ [conj]
  putStrLn []


-- | Print main proof type signature, and top level LHS ans RHS of the form
--
-- @
--   proofName : axiom₀ → ... → axiomₙ → conjecture
--   proofName axiomName₀ ... axiomNameₙ = subGoalImplName subgoal₀ ... subgoalₙ
--     where
-- @
printProofBody ∷ [F]    -- ^ Axioms
         → F            -- ^ Conjecture
         → String       -- ^ Function name (@proofName@)
         → [F]          -- ^ Subgoals
         → String       -- ^ Name of @subGoalImplName@
         → IO ()
printProofBody axioms conj proofName subgoals goalsName = do

  let f ∷ [Formula]
      f  = map formula $ axioms ++ [conj]

  let γ ∷ String
      γ = concatMap (\m → "{" ++ show m ++ "}") $ getFreeVars f

  let ρ ∷ String
      ρ = proofName ▪ γ

  print $ Signature proofName f
  putStrLn $ foldl (▪) ρ (map name axioms)
             ▪ "="
             ▪ foldl (▪) goalsName (map name subgoals)
  putStrLnInd 2 "where"

-- | For a given subgoal print each formula definition in reverse order
-- of dependencies
--
-- @
--       negation₀ : ¬ τ₀ → ⊥
--       negation₀ negate₀ = refute₀
--         where
--           step₀_ᵢ = fun-step₀_ᵢ step₀_ᵢ₁ .. step₀_ᵢⱼ
--           ...
--           step₀_₀ = fun-step₀_₀ step₀_₀₁ .. step₀_₀ₖ
--       subgoal₀ = proofByContradiction negation₀
--       ...
--       negationₙ : ¬ τₙ → ⊥
--       negationₙ negateₙ = refuteₙ
--         where
--           stepₙ_ₜ = fun-stepₙ_ₜ stepₙ__ₜ₁ .. stepₙ_ₜₒ
--           ...
--           stepₙ_₀ = fun-stepₙ_₀ stepₙ_₀₁ .. stepₙ_₀ᵤ
--       subgoal₀ = proofByContradiction negationₙ
-- @
--
-- This is perhaps the most important step and the one that does the
-- "actual" proof translation. The basic principle is to define each
-- @subgoal@ in terms of its parents which for most (if not all) cases
-- implies a @negation@ of the @subgoal@ and a corresponding @refute@
-- term.

printProofWhere ∷ ProofMap → ProofTree → IO ()
printProofWhere m t = do
  let subgoal = fromMaybe (error "No subgoal") $ F.find (isPrefixOf "subgoal") t
  let snegate = fromMaybe (error "No negate")  $ F.find (isPrefixOf "negate")  t
  _ ← printProofWhereBody 4 m t empty
  putStrLnInd 4 $  subgoal ▪ "=" ▪ "proofByContradiction" ▪ ("fun-" ++ snegate)
  return ()

printProofWhereBody ∷ Int → ProofMap → ProofTree → IdSet → IO (Int, String, IdSet)
printProofWhereBody _ _ (Leaf _ a)         _  = return (4, a, empty)
printProofWhereBody _ _ (Root Strip a _) _    = return (4, a, empty)
printProofWhereBody ind m (Root r a p) ω      =
    if checkIdScope ind a ω
      then return (4, a, empty)
      else do
        let scopeFold (i, aa, s) b = do
              (i₀,a₀,s₀) ← printProofWhereBody i m b s
              return (max i i₀, aa ▪ a₀, s `union` s₀)
        (ξ,ρ,s) ← foldM scopeFold (ind, "fun-" ++ a, insert (ind, a) ω ) p
        case r of
          Negate → do
            let f ∷ F
                f = fromMaybe (error "Error formula not found") (M.lookup a m)

            printInd ξ $ ScopedSignature ("fun-" ++ a) [formula f,bottom]

            let negLHS = swapPrefix "negate" "refute" a

            putStrLnInd ξ $ ("fun-" ++ a) ▪ a ▪ "=" ▪ negLHS
            putStrLnInd (ξ + 2) "where"
            return (ξ + 4, a,s)

          _      → do
            putStrLnInd ξ $ a ▪ "=" ▪ ρ
            return (ξ,a,s)
