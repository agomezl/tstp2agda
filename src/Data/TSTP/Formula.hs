
-- | Data.TSTP.Formula module

{-# OPTIONS -fno-warn-incomplete-patterns #-}

{-# LANGUAGE CPP                          #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE OverlappingInstances         #-}
{-# LANGUAGE UnicodeSyntax                #-}


module Data.TSTP.Formula where


import           Data.Function        (on)
import           Data.Monoid          (mappend)
import           Data.Set             (Set, difference, empty, fromList,
                                       singleton, toList, unions)
import           Data.TSTP.AtomicWord (AtomicWord (..))
import           Data.TSTP.BinOp      (BinOp (..))
import           Data.TSTP.InfixPred  (InfixPred (..))
import           Data.TSTP.Quant      (Quant (..))
import           Data.TSTP.Term       (Term (..)) 
import           Data.TSTP.V          (V (..))
import           Utils.Functions      (βshow, (▪), (<>))


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
             deriving (Eq, Ord, Read)

-- Pretty print instance of Show for Formula and Term
instance Show Formula where
  -- To avoid confusion every α → β is printed as (α → β)
  show (BinOp     f₁  (:=>:) f₂) = '(' <> f₁ ▪ '→' ▪ f₂ <> ')'
  show (BinOp     f₁  op     f₂) = f₁ ▪ op ▪ f₂
  show (InfixPred t₁  r      t₂) = t₁ ▪ r  ▪ t₂
  -- Predicates are just functions that return ⊤ with some parameter
  show (PredApp   ρ          []) = show ρ
  show (PredApp   ρ          φ ) = '(' <> ρ ▪ ':' ▪ φ ▪ "→ ⊤" <> ')'
  show (Quant     All []     f ) = βshow f
  show (Quant     All υ      f ) = '(' <> foldl (▪) "{" υ  ▪ ": Set}" ▪ '→' ▪ f <> ')'
  show (Quant     Exists υ   f ) = '(' <> foldl (▪) "{" υ  ▪ ": Set}" ▪ '→' ▪ f <> ')'
  show ((:~:)                f ) = '¬' ▪ f

-- Overlaped instance of Show [Formula] for "easy" representation of
-- x₁ ∧ x₂ ⊢ y₀ as x₀ → x₁ → y₀
#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPING #-} Show [Formula] where
#else
instance Show [Formula] where
#endif
  show []       = []
  show φ@(x:xs) = fvars ▪ foldl ((▪) . (▪ '→')) (βshow x) xs
      where
        fvars = case getFreeVars φ of
          [] → []
          (y:ys) → '{'  <> foldl (▪) (βshow y) ys ▪ ": Set} →"


-- | 'freeVarsF' 'f', returns a 'Set' of all free variables of 'f'.
freeVarsF ∷ Formula → Set V
freeVarsF ((:~:) x)                           = freeVarsF x
freeVarsF (BinOp x _ y)                       = (mappend `on` freeVarsF) x y
freeVarsF (InfixPred x _ y)                   = (mappend `on` freeVarsT) x y
freeVarsF (PredApp (AtomicWord "$false") [])  = empty
freeVarsF (PredApp (AtomicWord v) [])         = singleton $ V v
freeVarsF (PredApp _ args)                    = unions (fmap freeVarsT args)
freeVarsF (Quant _ vars x)                    = difference fvarsx lvars
  where
    fvarsx ∷ Set V
    fvarsx = freeVarsF x

    lvars  = fromList vars

-- | 'freeVarsT' 't', returns a 'Set' of all free variables of 't'.
freeVarsT ∷ Term → Set V
freeVarsT (FunApp _ args) = unions (fmap freeVarsT args)
freeVarsT (Var x)         = singleton x
freeVarsT _               = empty

-- | 'getFreeVars' 'f', given a list of formulas 'f' return all free
-- variables in the formulas.
getFreeVars ∷ [Formula] → [V]
getFreeVars = toList . unions . map freeVarsF
