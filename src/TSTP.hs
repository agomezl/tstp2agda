{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : TSTP
-- Author : Alejandro Gómez-Londoño
-- Date   : Sun Nov 22 16:18:58 2015
-- Description : Main library functions
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------
module TSTP (parse, parseFile) where

import TSTP.Parser        (parseTSTP)
import TSTP.Lexer         (alexScanTokens)
import Data.TSTP          (F)

-- | Parse a TSTP file and return a list of `F` formulas in no
-- particular order, for example:
-- @
--   cat examples/proof/Basic-1.tstp
--   fof(a1, axiom, (a)).
--   fof(a2, axiom, (b)).
--   fof(a3, axiom, ((a & b) => z)).
--   ...
-- @
-- would be:
-- @
--   [
--     F {name = "a1", role = Axiom, formula = a, source = NoSource},
--     F {name = "a2", role = Axiom, formula = b, source = NoSource},
--     F {name = "a3", role = Axiom, formula = ( a ∧ b → z ), source = NoSource},
--     ...
--   ]
-- @
parse :: String -> [F]
parse = parseTSTP . map snd . alexScanTokens

-- | Similar to `parse` but reading directly from a file.
parseFile :: FilePath -> IO [F]
parseFile x = parse `fmap` readFile x
