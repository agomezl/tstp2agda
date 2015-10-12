{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Base
-- Author : Alejandro Gómez Londoño
-- Date   : Sat Apr 18 14:11:27 2015
-- Description : Basic functions for parsing
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------

module TSTP.Base where

import Data.TSTP
import Data.Function (on)
import Data.Set (Set,toList,fromList,difference,unions,singleton,empty)
import Data.Monoid (mappend)

--TODO: implement this
univquant_free_vars :: Formula -> Formula
univquant_free_vars cnf = Quant All free_vars cnf
    where free_vars = toList $ freeVarsF cnf

freeVarsF ∷ Formula → Set V
freeVarsF ((:~:) x)         = freeVarsF x
freeVarsF (Quant _ vars x)  = difference (freeVarsF x) (fromList vars)
freeVarsF (BinOp x _ y)     = (mappend `on` freeVarsF) x y
freeVarsF (InfixPred x _ y) = (mappend `on` freeVarsT) x y
freeVarsF (PredApp _ args)  = unions (fmap freeVarsT args)

freeVarsT ∷ Term → Set V
freeVarsT (Var x)         = singleton x
freeVarsT (FunApp _ args) = unions (fmap freeVarsT args)
freeVarsT _               = empty



readRole ∷ String → Role
readRole "axiom"               = Axiom
readRole "hypothesis"          = Hypothesis
readRole "definition"          = Definition
readRole "assumption"          = Assumption
readRole "lemma"               = Lemma
readRole "theorem"             = Theorem
readRole "conjecture"          = Conjecture
readRole "negated_conjecture"  = NegatedConjecture
readRole "plain"               = Plain
readRole "fi_domain"           = FiDomain
readRole "fi_functors"         = FiFunctors
readRole "fi_predicates"       = FiPredicates
readRole "type"                = Type
readRole _                     = Unknown

binOp ∷ BinOp → Formula → Formula → Formula
binOp op f1 f2 = BinOp f1 op f2

readRule ∷ String → Rule
readRule "simplify"     = Simplify
readRule "negate"       = Negate
readRule "canonicalize" = Canonicalize
readRule "strip"        = Strip
readRule str            = NewRule str

readType ∷ String → IntroType
readType "definition"      = Definition_
readType "axiom_of_choice" = AxiomOfChoice
readType "tautology"       = Tautology
readType "assumption"      = Assumption_
readType _                 = UnknownType

readWord ∷ AtomicWord → String
readWord (AtomicWord a) = a

readStatus ∷ String → Status
readStatus "suc" = Suc
readStatus "unp" = Unp
readStatus "sap" = Sap
readStatus "esa" = Esa
readStatus "sat" = Sat
readStatus "fsa" = Fsa
readStatus "thm" = Thm
readStatus "eqv" = Eqv
readStatus "tac" = Tac
readStatus "wec" = Wec
readStatus "eth" = Eth
readStatus "tau" = Tau
readStatus "wtc" = Wtc
readStatus "wth" = Wth
readStatus "cax" = Cax
readStatus "sca" = Sca
readStatus "tca" = Tca
readStatus "wca" = Wca
readStatus "cup" = Cup
readStatus "csp" = Csp
readStatus "ecs" = Ecs
readStatus "csa" = Csa
readStatus "cth" = Cth
readStatus "ceq" = Ceq
readStatus "unc" = Unc
readStatus "wcc" = Wcc
readStatus "ect" = Ect
readStatus "fun" = Fun
readStatus "uns" = Uns
readStatus "wuc" = Wuc
readStatus "wct" = Wct
readStatus "scc" = Scc
readStatus "uca" = Uca
readStatus "noc" = Noc
readStatus _     = Unk
