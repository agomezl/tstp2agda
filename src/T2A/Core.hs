
-- | Core module

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax       #-}


module T2A.Core where

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
import           Util       (βshow, (▪))


-- Single function signature
-- | An  Agda type signature @α : τ@
data AgdaSignature = Signature String [Formula]
                   -- ^ Regular top level signature
                   | ScopedSignature String [Formula]
                   -- ^ Fully scoped signature with no newly
                   -- introduced type variables
                   deriving (Eq)

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

      if elem γ [Axiom, Conjecture]
        then Nothing
        else return $ Signature ("fun-" ++ φ) (ρ ++ [ζ])

-- | Retrieve signature name
fname ∷ AgdaSignature → String
fname (Signature       a _) = a
fname (ScopedSignature a _) = a

-- Pretty prints an `AgdaSignature`
instance Show AgdaSignature where
    show (ScopedSignature α (x:xs)) = α ▪ ":" ▪ ρ
    show (Signature α ρ)            = α ▪ ":" ▪ ρ
        where
          ρ = foldl ((▪) . (▪ '→')) (βshow x) xs

instance Ord AgdaSignature where
    a <= b = fname a <= fname b
