{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : TSTP
-- Author : Alejandro Gómez Londoño
-- Date   : Wed Feb 11 00:29:30 2015
-- Description : TSPT Data Types
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------

module Data.TSTP where


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
             deriving (Eq,Ord,Show,Read)

data Term = Var V                             -- ^ Variable
          | NumberLitTerm Rational            -- ^ Number literal
          | DistinctObjectTerm String         -- ^ Double-quoted item
          | FunApp AtomicWord [Term]          -- ^ Function symbol application
                                              -- (constants are encoded as
                                              -- nullary functions)
          deriving (Eq,Ord,Show,Read)

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
               deriving (Eq,Ord,Show,Read)

-- | /Term -> Term -> Formula/ infix connectives
data InfixPred =  (:=:) | (:!=:)
                  deriving (Eq,Ord,Show,Read)

-- | Quantifier specification
data Quant = All | Exists
             deriving (Eq,Ord,Show,Read)

newtype AtomicWord = AtomicWord String
    deriving (Eq,Ord,Show,Read)

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
