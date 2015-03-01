{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Parser
-- Author : Alejandro Gómez Londoño
-- Date   : Wed Feb 11 00:25:33 2015
-- Description : TSTP parsec parser
--------------------------------------------------------------------------------
-- Change log :
-- <Sun Feb 22 16:37:48 2015>
-- > Trow all of my parser away because of logic-tptp
--
--------------------------------------------------------------------------------


module TSTP.Parser where

import qualified Codec.TPTP.Base as Λ (Formula0(..),Term0(..))
import Codec.TPTP.Base ( F(..),T(..),AtomicWord(..), TPTP_Input_(..),Role(..))
import Data.Functor.Identity (Identity(..))
import Data.TSTP (Formula(..), Term(..),Role(..))
import qualified Data.TSTP as Ω (F(..),Fmap)
import Data.Map (fromList)



fΔ ∷ F Identity → Formula
fΔ (F (Identity f)) = fΓ f where
  fΓ (Λ.BinOp     f₀ op  f₁) = BinOp     (fΔ f₀) op          (fΔ f₁)
  fΓ (Λ.InfixPred t₀ iop t₁) = InfixPred (tΔ t₀) iop         (tΔ t₁)
  fΓ (Λ.PredApp   f₀ ts    ) = PredApp    f₀     (map tΔ ts)
  fΓ (Λ.Quant     q  vs  f₀) = Quant      q      vs          (fΔ f₀)
  fΓ ((Λ.:~:)     f₀       ) = (:~:)      (fΔ f₀)

tΔ ∷ T Identity → Term
tΔ (T (Identity t)) = tΓ t where
  tΓ (Λ.Var                v    ) = Var v
  tΓ (Λ.NumberLitTerm      r    ) = NumberLitTerm      r
  tΓ (Λ.DistinctObjectTerm s    ) = DistinctObjectTerm s
  tΓ (Λ.FunApp             s  t₀) = FunApp             s  (map tΔ t₀)

pΔ ∷ TPTP_Input_ Identity → Ω.F
pΔ (AFormula n r f a) = Ω.F n' r' f' a where
  AtomicWord n' = n
  f' = fΔ f
  r' = case r of
        (Role "hypothesis" )         → Hypothesis
        (Role "definition" )         → Definition
        (Role "assumption" )         → Assumption
        (Role "lemma" )              → Lemma
        (Role "theorem" )            → Theorem
        (Role "conjecture" )         → Conjecture
        (Role "negated_conjecture" ) → NegatedConjecture
        (Role "plain" )              → Plain
        (Role "fi_domain" )          → FiDomain
        (Role "fi_functors" )        → FiFunctors
        (Role "fi_predicates" )      → FiPredicates
        (Role "type" )               → Type
        _                            → Unknown

mΔ ∷ [Ω.F] → Ω.Fmap
mΔ lst = fromList $ map (\x → (Ω.name x, x)) lst
