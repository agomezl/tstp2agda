module Main where

open import IO.Primitive using (IO;_>>=_)
open import TSTP.Parser using (runTest;Unit)
open import Data.String.Base using (String)

postulate
  getLine : IO String

{-# COMPILED getLine getLine #-}

main : IO Unit
main = getLine >>= runTest
