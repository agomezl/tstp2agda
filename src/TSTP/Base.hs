
-- | Base module

{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_HADDOCK hide   #-}


module TSTP.Base where

import           Data.Function (on)
import           Data.Monoid   (mappend)
import           Data.Set      (Set, difference, empty, fromList, singleton,
                                toList, unions)
import           Data.TSTP
import           Util          (agdafy)


univquant_free_vars ∷ Formula → Formula
univquant_free_vars cnf = Quant All free_vars cnf
    where free_vars = toList $ freeVarsF cnf

readRole ∷ String → Role
readRole "assumption"         = Assumption
readRole "axiom"              = Axiom
readRole "conjecture"         = Conjecture
readRole "definition"         = Definition
readRole "fi_domain"          = FiDomain
readRole "fi_functors"        = FiFunctors
readRole "fi_predicates"      = FiPredicates
readRole "hypothesis"         = Hypothesis
readRole "lemma"              = Lemma
readRole "negated_conjecture" = NegatedConjecture
readRole "plain"              = Plain
readRole "theorem"            = Theorem
readRole "type"               = Type
readRole _                    = Unknown

binOp ∷ BinOp → Formula → Formula → Formula
binOp op f1 f2 = BinOp f1 op f2

readRule ∷ String → Rule
readRule "canonicalize" = Canonicalize
readRule "negate"       = Negate
readRule "simplify"     = Simplify
readRule "strip"        = Strip
readRule str            = NewRule str

readType ∷ String → IntroType
readType "assumption"      = Assumption_
readType "axiom_of_choice" = AxiomOfChoice
readType "definition"      = Definition_
readType "tautology"       = Tautology
readType _                 = UnknownType

readWord ∷ AtomicWord → String
readWord (AtomicWord a) = agdafy a

readStatus ∷ String → Status
readStatus "cax" = Cax
readStatus "ceq" = Ceq
readStatus "csa" = Csa
readStatus "csp" = Csp
readStatus "cth" = Cth
readStatus "cup" = Cup
readStatus "ecs" = Ecs
readStatus "ect" = Ect
readStatus "eqv" = Eqv
readStatus "esa" = Esa
readStatus "eth" = Eth
readStatus "fsa" = Fsa
readStatus "fun" = Fun
readStatus "noc" = Noc
readStatus "sap" = Sap
readStatus "sat" = Sat
readStatus "sca" = Sca
readStatus "scc" = Scc
readStatus "suc" = Suc
readStatus "tac" = Tac
readStatus "tau" = Tau
readStatus "tca" = Tca
readStatus "thm" = Thm
readStatus "uca" = Uca
readStatus "unc" = Unc
readStatus "unp" = Unp
readStatus "uns" = Uns
readStatus "wca" = Wca
readStatus "wcc" = Wcc
readStatus "wct" = Wct
readStatus "wec" = Wec
readStatus "wtc" = Wtc
readStatus "wth" = Wth
readStatus "wuc" = Wuc
readStatus _     = Unk
