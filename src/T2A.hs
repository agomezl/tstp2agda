{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : T2A
-- Author : Alejandro Gómez-Londoño
-- Date   : Fri Nov 27 14:01:12 2015
-- Description :
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------

module T2A (
           -- * How to use tstp2agda
           -- | Let use an example, given this problem
           --
           -- @
           --   $ cat problem.tstp
           --   fof(a1,axiom,a).
           --   fof(a2,conjecture,a).
           -- @
           --
           -- and the corresponding
           -- <http://www.gilith.com/software/metis/  Metis>
           -- proof
           --
           -- @
           --   $ cat proof.tstp
           --   ---------------------------------------------------------------------------
           --   SZS status Theorem for examples/problem/Test-1.tstp
           --   SZS output start CNFRefutation for examples/problem/Test-1.tstp
           --   fof(a1, axiom, (a)).
           --   fof(a2, conjecture, (a)).
           --   fof(subgoal_0, plain, (a), inference(strip, [], [a2])).
           --   fof(negate_0_0, plain, (~ a), inference(negate, [], [subgoal_0])).
           --   fof(normalize_0_0, plain, (~ a),
           --       inference(canonicalize, [], [negate_0_0])).
           --   fof(normalize_0_1, plain, (a), inference(canonicalize, [], [a1])).
           --   fof(normalize_0_2, plain, ($false),
           --       inference(simplify, [], [normalize_0_0, normalize_0_1])).
           --   cnf(refute_0_0, plain, ($false),
           --       inference(canonicalize, [], [normalize_0_2])).
           --   SZS output end CNFRefutation for examples/problem/Test-1.tstp
           -- @
           -- we create some requiered data structures
           --
           -- @
           -- main ∷ IO ()
           -- main = do
           --   -- read the file
           --   formulas ← 'parseFile' "proof.tstp"
           --   -- create a map
           --   proofmap ← 'buildProofMap' formulas
           --   -- get subgoals,refutes,axioms, and the conjecture
           --   let subgoals    = 'getSubGoals' formulas
           --   let refutes     = 'getRefutes' formulas
           --   let axioms      = 'getAxioms' formulas
           --   let (Just conj) = 'getConjeture' formulas
           --   -- build a 'proofTree' for each subgoal (using his associated refute)
           --   let prooftree = 'map' ('buildProofTree' proofmap) refutes
           -- @
           --
           -- and then print the actual Agda code
           -- @
           --   -- PREAMBLE: module definitions and imports
           --   'printPreamble' \"BaseProof\"
           --   -- STEP 1: Print auxiliary functions
           --   'printAuxSignatures' proofmap prooftree
           --   -- STEP 2: Subgoal handling
           --   'printSubGoals' subgoals conj "goals"
           --   -- STEP 3: Print main function signature
           --   'printProofBody' axioms conj "proof" subgoals "goals"
           --   -- STEP 4: Print all the step of the proof as local definitions
           --   'mapM_' ('printProofWhere' proofmap  prooftree
           -- @
           --
           -- and then get
           --
           -- @
           --   module BaseProof where
           --   open import Data.FOL.Shallow
           --   postulate fun-normalize-0-0 : { a : Set} → ¬ a → ¬ a
           --   postulate fun-normalize-0-1 : { a : Set} → a → a
           --   postulate fun-normalize-0-2 : { a : Set} → ¬ a → a → ⊥
           --   postulate fun-refute-0-0 :  ⊥ → ⊥
           --   postulate goals : { a : Set} → a → a
           --   proof : { a : Set} → a → a
           --   proof {a} a1 = goals subgoal-0
           --     where
           --       fun-negate-0-0 : ¬ a → ⊥
           --       fun-negate-0-0 negate-0-0 = refute-0-0
           --         where
           --           normalize-0-0 = fun-normalize-0-0 negate-0-0
           --           normalize-0-1 = fun-normalize-0-1 a1
           --           normalize-0-2 = fun-normalize-0-2 normalize-0-0 normalize-0-1
           --           refute-0-0 = fun-refute-0-0 normalize-0-2
           --       subgoal-0 = proofByContradiction fun-negate-0-0
           -- @
           --

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

import Data.TSTP          (Role(Axiom,Conjecture),F,role,name,formula,bottom)
import Data.TSTP          (Rule(Negate,Strip),getFreeVars)
import Data.List          (find,isPrefixOf)
import Data.Map as M      (lookup)
import TSTP               (parseFile)
import Data.Proof         (buildProofMap,buildProofTree,ProofMap,ProofTree)
import Data.Maybe         (catMaybes, fromMaybe)
import Data.Proof         (ProofTreeGen(..))
import Data.Foldable      (toList)
import Control.Monad      (foldM)
import T2A.Core           (buildSignature)
import T2A.Core           (AgdaSignature(Signature,ScopedSignature))
import Util               ((▪),unique,printInd,putStrLnInd,swapPrefix)

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
printAuxSignatures ω γ = mapM_ lineP signatures
    where signatures = unique . concat . map signature $ γ
          signature t = catMaybes -- Remove Nothings
                        . toList  -- Flatten the tree
                                  -- Build (only) the requiered functions
                        . fmap (buildSignature ω) $ t
          lineP s = (putStrLn $ "postulate" ▪ s) >> putStrLn []


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
  (i,a) ← printProofWhereBody 4 m t
  putStrLnInd 4 $  subgoal ▪ "=" ▪ "proofByContradiction" ▪ ("fun-" ++ negate)
  return ()

printProofWhereBody ∷ Int → ProofMap → ProofTree → IO (Int,String)
printProofWhereBody _ _ (Leaf _ a)         = return (4,a)
printProofWhereBody ind _ (Root Strip a _) = return (4,a)
printProofWhereBody ind m (Root r a p) = do
  let scopeFold (i,a) b = do
        (i₀,a₀) ← printProofWhereBody i m b
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
