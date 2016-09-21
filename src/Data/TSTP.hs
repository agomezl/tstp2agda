
-- | Data.TSTP module

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UnicodeSyntax        #-}

#ifndef MIN_VERSION_base
#define MIN_VERSION_base(a,b,c) 1
#endif

module Data.TSTP
  ( F(..)
  , Role(..)
  -- * Formulas and terms
  , Formula(..)
  , Term(..)
  -- ** 'Show' instances
  -- | 'Formula', 'Term' and other data types in this section
  -- have 'Show' instances that allow pretty-printing
  -- of 'Formulas' and 'Show' @['Formula']@ is an
  -- especial instance that print its contents as
  -- sequence of implications
  --
  -- >>> let f1 = PredApp (AtomicWord "a") []
  -- >>> let f2 = PredApp (AtomicWord "b") []
  -- >>> let f3 = (BinOp (PredApp (AtomicWord "a") []) (:&:) (PredApp (AtomicWord "b") []))
  -- >>> f1
  -- a
  -- >>> f2
  -- b
  -- >>> f3
  -- a ∧ b
  -- >>> [f1,f2,f3]
  -- { a b : Set} → a → b → a ∧ b
  --
  -- Some syntax sugar is also present
  --
  -- >>> PredApp (AtomicWord "$false") []
  -- ⊥
  , AtomicWord(..)
  , BinOp(..)
  , InfixPred(..)
  , Quant(..)
  , V(..)
  -- * Source information
  , Parent(..)
  , Rule(..)
  , Source(..)
  -- * Functions
  , bottom
  , freeVarsF
  , freeVarsT
  , getFreeVars
  , isBottom
  -- * Unused types
  -- | The following types are required to have full
  -- support of the TSTP syntax but haven't been used yet
  -- in 'tstp2agda' aside from the parser.
  , GData(..)
  , GTerm(..)
  , Info(..)
  , IntroType(..)
  , Status(..)
  , Theory(..)
  ) where

import           Data.Function (on)
import           Data.Monoid   (mappend)
import           Data.Set      (Set, difference, empty, fromList, singleton,
                                toList, unions)
import           Util          (βshow, (▪))



-- | Formula roles.
data Role = Assumption
          | Axiom
          | Conjecture
          | Definition
          | FiDomain
          | FiFunctors
          | FiPredicates
          | Hypothesis
          | Lemma
          | NegatedConjecture
          | Plain
          | Theorem
          | Type
          | Unknown
          deriving (Eq, Ord, Show, Read)

-- | Main formula type, it contains all the elements and information
-- of a TSTP formula definition. While 'name', 'role', and 'formula'
-- are self-explanatory, 'source' is a messy meta-language in itself,
-- different ATPs may embed different amounts of information in it.
data F = F
  { formula ∷ Formula
  , name    ∷ String
  , role    ∷ Role
  , source  ∷ Source
  }
  deriving (Eq, Ord, Show, Read)

-- | 'Source' main purpose is to provide all the information regarding
-- the deductive process that lead to a given formula. Information
-- about the rules applied along with parent formulas and
-- <http://www.cs.miami.edu/~tptp/TPTP/TPTPTParty/2007/PositionStatements/GeoffSutcliffe_SZS.html SZS>
-- status are among the information you might expect from this field.
data Source = Creator String [Info]
            | File String (Maybe String)
            | Inference Rule [Info] [Parent]
            | Introduced IntroType [Info]
            | Name String
            | NoSource
            | Source String
            | Theory Theory [Info]
            deriving (Eq, Ord, Show, Read)

-- | Parent formula information.
data Parent = Parent String [GTerm]
              deriving (Eq, Ord, Show, Read)


-- | Deduction rule applied.
data Rule   = Canonicalize
            | Negate
            | NewRule String
            | Simplify
            | Strip
            deriving (Eq, Ord, Show, Read)

-- NOT BEING USED YET
data IntroType = Assumption_
               | AxiomOfChoice
               | Definition_
               | Tautology
               | UnknownType
               deriving (Eq, Ord, Show, Read)

-- NOT BEING USED YET
data Theory = Equality | AC
            deriving (Eq, Ord, Show, Read)

-- NOT BEING USED YET
data Info   = AssumptionR [String]
            | Description String
            | Function String [GTerm]
            | InferenceInfo Rule String [GTerm]
            | IQuote String
            | Refutation Source
            | Status Status
            deriving (Eq, Ord, Show, Read)

-- NOT BEING USED YET
data Status = Cax
            | Ceq
            | Csa
            | Csp
            | Cth
            | Cup
            | Ecs
            | Ect
            | Eqv
            | Esa
            | Eth
            | Fsa
            | Fun
            | Noc
            | Sap
            | Sat
            | Sca
            | Scc
            | Suc
            | Tac
            | Tau
            | Tca
            | Thm
            | Uca
            | Unc
            | Unk
            | Unp
            | Uns
            | Wca
            | Wcc
            | Wct
            | Wec
            | Wtc
            | Wth
            | Wuc
            deriving (Eq, Ord, Show, Read)

-- The following code is based on:
-- https://github.com/DanielSchuessler/logic-TPTP
-- and is just a simplified version of the the datatypes
-- (without the Indirect composite)

-- | first-order logic formula.
data Formula = BinOp Formula BinOp Formula    -- ^ Binary connective application
             | InfixPred Term InfixPred Term  -- ^ Infix predicate application
             | PredApp AtomicWord [Term]      -- ^ Predicate application
             | Quant Quant [V] Formula        -- ^ Quantified Formula
             | (:~:) Formula                  -- ^ Negation
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

-- Overlaped instance of Show [Formula] for "easy" representation of
-- x₁ ∧ x₂ ⊢ y₀ as x₀ → x₁ → y₀
#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPING #-} Show [Formula] where
#else
instance Show [Formula] where
#endif
  show []     = []
  show φ@(x:xs) = fvars ▪ foldl ((▪) . (▪ '→')) (βshow x) xs
      where
        fvars = case getFreeVars φ of
                      [] → []
                      (y:ys) → '{' ▪ foldl (▪) (βshow y) ys ▪ ": Set} →"

-- | First-order logic terms.
data Term = Var V                             -- ^ Variable
          | NumberLitTerm Rational            -- ^ Number literal
          | DistinctObjectTerm String         -- ^ Double-quoted item
          | FunApp AtomicWord [Term]          -- ^ Function symbol application
                                              -- (constants are encoded as
                                              -- nullary functions)
          deriving (Eq,Ord,Read)

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

-- | Variable
newtype V = V String
    deriving (Eq,Ord,Read)

instance Show V where
    show (V a) = a

-- | Binary formula connectives.
data BinOp =   (:<=>:)  -- ^ ↔ /Equivalence/
            |  (:=>:)   -- ^ → /Implication/
            |  (:<=:)   -- ^ ← /Reverse Implication/
            |  (:&:)    -- ^ ∧ /AND/
            |  (:|:)    -- ^ ∨ /OR/
            |  (:~&:)   -- ^ ⊼ /NAND/
            |  (:~|:)   -- ^ ⊽ /NOR/
            |  (:<~>:)  -- ^ ⊕ /XOR/
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

-- | Infix connectives of the form /Term -> Term -> Formula/.
data InfixPred =  (:=:)  -- ^ =
               |  (:!=:) -- ^ ≠
                  deriving (Eq,Ord,Read)

instance Show InfixPred where
    show (:=:)  = "="
    show (:!=:) = "≠"

-- | Quantifier specification.
data Quant = All    -- ^ ∀
           | Exists -- ^ ∃
             deriving (Eq, Ord, Show, Read)

newtype AtomicWord = AtomicWord String
    deriving (Eq,Ord,Read)

instance Show AtomicWord where
    show (AtomicWord "$false") = "⊥"
    show (AtomicWord a) = a

-- | 'getFreeVars' 'f', given a list of formulas 'f' return all free
-- variables in the formulas.
getFreeVars ∷ [Formula] → [V]
getFreeVars = toList . unions . map freeVarsF

-- | 'isBottom' 'f', test whether 'f' = ⊥.
isBottom ∷ F → Bool
isBottom = (==) (PredApp (AtomicWord "$false") []) . formula

-- | 'bottom' = ⊥.
bottom ∷ Formula
bottom = PredApp (AtomicWord "$false") []

-- | 'freeVarsF' 'f', returns a 'Set' of all free variables of 'f'.
freeVarsF ∷ Formula → Set V
freeVarsF ((:~:) x)         = freeVarsF x
freeVarsF (Quant _ vars x)  = difference (freeVarsF x) (fromList vars)
freeVarsF (BinOp x _ y)     = (mappend `on` freeVarsF) x y
freeVarsF (InfixPred x _ y) = (mappend `on` freeVarsT) x y
freeVarsF (PredApp (AtomicWord "$false") [])  = empty
freeVarsF (PredApp (AtomicWord v) [])         = singleton $ V v
freeVarsF (PredApp _ args)                    = unions (fmap freeVarsT args)

-- | 'freeVarsT' 't', returns a 'Set' of all free variables of 't'.
freeVarsT ∷ Term → Set V
freeVarsT (Var x)         = singleton x
freeVarsT (FunApp _ args) = unions (fmap freeVarsT args)
freeVarsT _               = empty

-- | Metadata (the /general_data/ rule in
--   <http://www.cs.miami.edu/~tptp/ TPTP>'s grammar)
data GData = GWord AtomicWord
                 | GApp AtomicWord [GTerm]
                 | GVar V
                 | GNumber Rational
                 | GDistinctObject String
                 | GFormulaData String Formula
                 | GFormulaTerm String Term
                 deriving (Eq, Ord, Show, Read)

-- | Metadata (the /general_term/ rule in
--   <http://www.cs.miami.edu/~tptp/ TPTP>'s grammar)
data GTerm = ColonSep GData GTerm
           | GTerm GData
           | GList [GTerm]
           deriving (Eq, Ord, Show, Read)
