module TSTP.Parser where

{-# IMPORT TSTP.Parser #-}
open import Data.String.Core using (String)
open import IO.Primitive using (IO)

data Unit : Set where unit : Unit
{-# COMPILED_DATA Unit () () #-}

postulate
  runTest : String → IO Unit

{-# COMPILED runTest TSTP.Parser.runTest #-}
