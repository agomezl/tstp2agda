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
import Codec.TPTP.Base ( F(..),T(..))
import Data.Functor.Identity (Identity(..))
import Data.TSTP (Formula(..), Term(..))



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
