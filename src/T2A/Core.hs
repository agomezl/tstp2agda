
-- | Core module

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax       #-}


module T2A.Core
  ( AgdaSignature
    ( Signature
    , ScopedSignature
    )
  , buildSignature
  ) where


import           Data.List  (isPrefixOf)
import           Data.Map   as M (lookup)
import           Data.Proof (ProofMap, getParents)

import  Data.TSTP
  ( F (..)
  , Formula (..)
  , Role (..)
  , Source (..)
  , isBottom
  )

import           Utils.Functions (βshow, (▪))


-- Single function signature
-- | An  Agda type signature @α : τ@
data AgdaSignature = Signature String [Formula]
                   -- ^ Regular top level signature
                   | ScopedSignature String [Formula]
                   -- ^ Fully scoped signature with no newly
                   -- introduced type variables
                   deriving (Eq)

-- Pretty prints an `AgdaSignature`
instance Show AgdaSignature where
    show (Signature α ρ)            = α ▪ ":" ▪ ρ
    show (ScopedSignature α (x:xs)) = α ▪ ":" ▪ ρ
        where
          -- p ∷ String -- FIX
          ρ = foldl ((▪) . (▪ '→')) (βshow x) xs

instance Ord AgdaSignature where
    a <= b = fname a <= fname b

-- | Retrieve signature name
fname ∷ AgdaSignature → String
fname (Signature       a _) = a
fname (ScopedSignature a _) = a

-- | Given a proof map ω and some formula name φ, construct
-- the appropriated 'AgdaSignature' based on the parents of φ
buildSignature ∷ ProofMap → String → Maybe AgdaSignature
buildSignature ω φ
  | "subgoal" `isPrefixOf` φ = Nothing
  | "negate"  `isPrefixOf` φ = Nothing
  | otherwise                = do
      φ₁ ∷ F ← M.lookup φ ω

      let γ ∷ Role
          γ = role φ₁

      let ζ ∷ Formula
          ζ = formula φ₁

      let β ∷ Source
          β = source φ₁

      let ρ ∷ [Formula]
          ρ = case β of
            Inference _ _ ρ₁ → map formula $ getParents ω ρ₁
            _                → []

      if γ `elem` [Axiom, Conjecture]
        then Nothing
        else return $ Signature ("fun-" ++ φ) (ρ ++ [ζ])
