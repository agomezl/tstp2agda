
-- | TSTP module

{-# LANGUAGE CPP           #-}
{-# LANGUAGE UnicodeSyntax #-}


#ifndef MIN_VERSION_base
#define MIN_VERSION_base(a,b,c) 1
#endif
-- Assume we are using the newest versions when using ghci without cabal


module TSTP
  ( parse
  , parseFile
  ) where

import           Data.TSTP           (F)
import           System.IO           (getContents)
import           TSTP.Lexer          (alexScanTokens)
import           TSTP.Parser         (parseTSTP)

#if __GLASGOW_HASKELL__ <= 708
import           Control.Applicative ((<$>))
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

parse ∷ String → [F]
parse = parseTSTP . map snd . alexScanTokens

-- | Similar to `parse` but reading directly from a file or stdin.

parseFile ∷ Maybe FilePath → IO [F]
parseFile x = parse <$> case x of Just x  → readFile x
                                  _       → getContents
