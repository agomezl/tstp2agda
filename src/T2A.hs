
-- | T2A module

{-# LANGUAGE UnicodeSyntax #-}

module T2A (
   -- * Getters
     getSubGoals
   , getRefutes
   , getAxioms
   , getConjeture
   -- * <http://wiki.portal.chalmers.se/agda/pmwiki.php Agda> translation
   , printPreamble
   , printAuxSignatures
   , printSubGoals
   , printProofBody
   , printProofWhere
   , buildProofMap
   , buildProofTree
   -- * TSTP parsing
   , parseFile
   ) where

import           Control.Monad (foldM)
import           Data.Foldable (toList)
import           Data.List     (find, isPrefixOf)
import           Data.Map      as M (lookup)
import           Data.Maybe    (catMaybes, fromMaybe)
import           Data.Proof    (ProofMap, ProofTree, buildProofMap,
                                buildProofTree)
import           Data.Proof    (IdSet, ProofTreeGen (..))
import           Data.Set      as S (Set, empty, insert, singleton, union)
import           Data.TSTP     (F, Role (Axiom, Conjecture), bottom, formula,
                                name, role)
import           Data.TSTP     (Rule (Negate, Strip), getFreeVars)
import           T2A.Core      (buildSignature)
import           T2A.Core      (AgdaSignature (ScopedSignature, Signature))
import           T2A.Tactics   (resolveTacticGen)
import           TSTP          (parseFile)
import           Util          (printInd, putStrLnInd, unique, (▪))
import           Util          (checkIdScope, swapPrefix)

import qualified Data.Foldable as F (find)


-- | Extract subgoals from a list of formulae.
getSubGoals ∷ [F] → [F]
getSubGoals rules = filter (isPrefixOf "subgoal" . name) rules

-- | Extract refuting steps from a list of formulae.
getRefutes ∷ [F] → [F]
getRefutes rules = filter (isPrefixOf "refute"  . name) rules

-- | Extract axioms from a list of formulae.
getAxioms ∷ [F] → [F]
getAxioms rules = filter ((==) Axiom      . role) rules

-- | Try to extract a conjecture from a list of formulae and checks
-- for uniqueness.
getConjeture ∷ [F] → Maybe F
getConjeture rules =  case filter ((==) Conjecture . role) rules of
                        [l] → Just l
                        _   → Nothing

printPreamble ∷ String -- ^ Module name
              → IO ()
printPreamble moduleName = do
  putStrLn $ "module" ▪ moduleName ▪ "where"
  putStrLn $ "open import Data.FOL.Shallow"
  putStrLn $ "open import Function using (id)"
  putStrLn []

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
    where signatures = unique . concat . map signature $ γ
          signature t = catMaybes -- Remove Nothings
                        . toList  -- Flatten the tree
                                  -- Build (only) the requiered functions
                        . fmap (buildSignature ω) $ t



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
  let f = map formula $ axioms ++ [conj]
  let γ = concat . map (\m → "{" ++ show m ++ "}") $ getFreeVars f
  let ρ = proofName ▪ γ
  print $ Signature proofName $ f
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
  let negate  = fromMaybe (error "No negate")  $ F.find (isPrefixOf "negate")  t
  (i,a,s) ← printProofWhereBody 4 m t empty
  putStrLnInd 4 $  subgoal ▪ "=" ▪ "proofByContradiction" ▪ ("fun-" ++ negate)
  return ()

printProofWhereBody ∷ Int → ProofMap → ProofTree → IdSet → IO (Int,String,IdSet)
printProofWhereBody _ _ (Leaf _ a)         _ = return (4,a,empty)
printProofWhereBody ind _ (Root Strip a _) _ = return (4,a,empty)
printProofWhereBody ind m (Root r a p) ω =
    if checkIdScope ind a ω
    then return (4,a,empty)
    else do
      let scopeFold (i,a,s) b = do
            (i₀,a₀,s₀) ← printProofWhereBody i m b s
            return (max i i₀, a ▪ a₀, s `union` s₀)
      (ξ,ρ,s) ← foldM scopeFold (ind,"fun-" ++ a,insert (ind,a) ω ) p
      case r of
        Negate → do
               let f = fromMaybe (error "Error formula not found") (M.lookup a m)
               printInd ξ $ ScopedSignature ("fun-" ++ a) [formula f,bottom]
               let negLHS = swapPrefix "negate" "refute" a
               putStrLnInd ξ $ ("fun-" ++ a) ▪ a ▪ "=" ▪ negLHS
               putStrLnInd (ξ + 2) "where"
               return (ξ + 4, a,s)
        _      → do
               putStrLnInd ξ $ a ▪ "=" ▪ ρ
               return (ξ,a,s)
