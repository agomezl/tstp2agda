{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleInstances #-}
--------------------------------------------------------------------------------
-- File   : TSTP
-- Author : Alejandro Gómez Londoño
-- Date   : Wed Feb 11 00:29:30 2015
-- Description : TSPT Data Types
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------

module Data.TSTP where

import Util ((▪),βshow)

data Role = Axiom
          | Hypothesis
          | Definition
          | Assumption
          | Lemma
          | Theorem
          | Conjecture
          | NegatedConjecture
          | Plain
          | FiDomain
          | FiFunctors
          | FiPredicates
          | Type
          | Unknown
          deriving (Eq,Ord,Show,Read)

data F = F { name    ∷ String,
             role    ∷ Role,
             formula ∷ Formula,
             source  ∷ Source
           }
       deriving (Eq,Ord,Show,Read)

data Source = Source String
            | Inference Rule [Info] [Parent]
            | Introduced IntroType [Info]
            | File String (Maybe String)
            | Theory Theory [Info]
            | Creator String [Info]
            | Name String
            | NoSource
            deriving (Eq,Ord,Show,Read)

data IntroType = Definition_
               | AxiomOfChoice
               | Tautology
               | Assumption_
               | UnknownType
                 deriving (Eq,Ord,Show,Read)
data Theory = Equality | AC
            deriving (Eq,Ord,Show,Read)

data Rule   = Simplify
            | Negate
            | Canonicalize
            | Strip
            | NewRule String
              deriving (Eq,Ord,Show,Read)

data Info   = Description String
            | IQuote String
            | Status Status
            | Function String [GTerm]
            | InferenceInfo Rule String [GTerm]
            | AssumptionR [String]
            | Refutation Source
              deriving (Eq,Ord,Show,Read)

data Status = Suc | Unp | Sap | Esa | Sat
            | Fsa | Thm | Eqv | Tac | Wec
            | Eth | Tau | Wtc | Wth | Cax
            | Sca | Tca | Wca | Cup | Csp
            | Ecs | Csa | Cth | Ceq | Unc
            | Wcc | Ect | Fun | Uns | Wuc
            | Wct | Scc | Uca | Noc | Unk
              deriving (Eq,Ord,Show,Read)


data Parent = Parent String [GTerm]
              deriving (Eq,Ord,Show,Read)

-- * General decorated formulae and terms

-- The following code is based on:
-- https://github.com/DanielSchuessler/logic-TPTP
-- and is just a simplified version of the the datatypes
-- (without the Indirect composite)

data Formula = BinOp Formula BinOp Formula    -- ^ Binary connective application
             | InfixPred Term InfixPred Term  -- ^ Infix predicate application
             | PredApp AtomicWord [Term]      -- ^ Predicate application
             | Quant Quant [V] Formula        -- ^ Quantified Formula
             | (:~:) Formula                  -- ^ Negation
             deriving (Eq,Ord,Read)

data Term = Var V                             -- ^ Variable
          | NumberLitTerm Rational            -- ^ Number literal
          | DistinctObjectTerm String         -- ^ Double-quoted item
          | FunApp AtomicWord [Term]          -- ^ Function symbol application
                                              -- (constants are encoded as
                                              -- nullary functions)
          deriving (Eq,Ord,Read)


-- Pretty print instance of Show for Formula and Term
instance Show Formula where
    -- To avoid confusion every α → β is printed as (α → β)
    show (BinOp     f₁  (:=>:) f₂) = '(' ▪ f₁   ▪ '→' ▪ f₂  ▪ ')'
    show (BinOp     f₁  op     f₂) = f₁  ▪ op   ▪ f₂
    show (InfixPred t₁  pred   t₂) = t₁  ▪ pred ▪ t₂
    -- Predicates are just functions that return ⊤ with some parameter
    show (PredApp   ρ          []) = show ρ
    show (PredApp   ρ          φ ) = '(' ▪ ρ    ▪ ':' ▪ φ   ▪ "→ ⊤" ▪ ')'
    show (Quant     All []     f ) = βshow f
    show (Quant     All υ      f ) = '(' ▪ foldl (▪) "{" υ  ▪ ": Set }" ▪ '→' ▪ f ▪ ')'
    show ((:~:)                f ) = '¬' ▪ f

instance {-# OVERLAPPING #-} Show [Formula] where
    show []     = []
    show (x:xs) = foldl ((▪) . (▪ '→')) (βshow x) xs

instance Show Term where
    show (Var             (V v))     =      v
    show (NumberLitTerm      r )     = show r
    show (DistinctObjectTerm t )     =      t
    show (FunApp (AtomicWord w ) []) =      w
    -- TODO: what functions are in Shallow.agda or in agda itself?
    show (FunApp (AtomicWord w ) [a]) = error "Don't really know what this is"



-- The following code is from:
-- https://github.com/DanielSchuessler/logic-TPTP
-- and is used with the propose of reuses his
-- alex/happy parser in a more simple way

newtype V = V String
    deriving (Eq,Ord,Show,Read)

-- | Binary formula connectives
data BinOp =   (:<=>:)  -- ^ Equivalence
            |  (:=>:)   -- ^ Implication
            |  (:<=:)   -- ^ Reverse Implication
            |  (:&:)    -- ^ AND
            |  (:|:)    -- ^ OR
            |  (:~&:)   -- ^ NAND
            |  (:~|:)   -- ^ NOR
            |  (:<~>:)  -- ^ XOR
               deriving (Eq,Ord,Read)

instance Show BinOp where
    show (:<=>:) = "↔"
    show (:=>:)  = "→"
    show (:<=:)  = "←"
    show (:&:)   = "∧"
    show (:|:)   = "∨"
    show (:~&:)  = "⊼"
    show (:~|:)  = "⊽"
    show (:<~>:) = "⊕"



-- | /Term -> Term -> Formula/ infix connectives
data InfixPred =  (:=:) | (:!=:)
                  deriving (Eq,Ord,Show,Read)

-- | Quantifier specification
data Quant = All | Exists
             deriving (Eq,Ord,Show,Read)

newtype AtomicWord = AtomicWord String
    deriving (Eq,Ord,Read)

instance Show AtomicWord where
    show (AtomicWord a) = a

-- | Metadata (the /general_data/ rule in TPTP's grammar)
data GData = GWord AtomicWord
                 | GApp AtomicWord [GTerm]
                 | GVar V
                 | GNumber Rational
                 | GDistinctObject String
                 | GFormulaData String Formula
                 | GFormulaTerm String Term
                   deriving (Eq,Ord,Show,Read)

-- | Metadata (the /general_term/ rule in TPTP's grammar)
data GTerm = ColonSep GData GTerm
           | GTerm GData
           | GList [GTerm]
             deriving (Eq,Ord,Show,Read)
