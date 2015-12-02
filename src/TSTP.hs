{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE CPP #-}
--------------------------------------------------------------------------------
-- File   : TSTP
-- Author : Alejandro Gómez-Londoño
-- Date   : Sun Nov 22 16:18:58 2015
-- Description : Main library functions
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------
#ifndef MIN_VERSION_base
#define MIN_VERSION_base(a,b,c) 1
#endif
-- Assume we are using the newest versions when using ghci without cabal


module TSTP (parse, parseFile) where

import TSTP.Parser        (parseTSTP)
import TSTP.Lexer         (alexScanTokens)
import System.IO          (getContents)
import Data.TSTP          (F)
#if MIN_VERSION_base(4,7,0)
import Control.Applicative ((<$>))
#endif

-- | Parse a TSTP file and return a list of `F` formulas in no
-- particular order, for example:
--
-- @
--   $ cat examples\/proof\/Basic-1.tstp
--   fof(a1, axiom, (a)).
--   fof(a2, axiom, (b)).
--   fof(a3, axiom, ((a & b) => z)).
--   ...
-- @
--
-- would be:
--
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

-- | Similar to `parse` but reading directly from a file or stdin.
parseFile :: Maybe FilePath -> IO [F]
parseFile x = parse <$> case x of Just x  → readFile x
                                  Nothing → getContents
