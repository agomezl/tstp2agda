{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Main
-- Author : Alejandro Gómez Londoño
-- Date   : Wed Mar 11 23:29:13 2015
-- Description : Main module
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------
module Main where

import System.Environment (getArgs)
import Args (compileOpts,helpmsg,Flag(..))
import TSTP.Parser (pΔ)
import System.Exit (exitFailure)
import Codec.TPTP (parseFile)

main :: IO ()
main = do
  args <- getArgs
  case compileOpts args of
   Left [File f] → fileMain f
   Left [Help]   → helpmsg
   Left _        → putStrLn "Bad parameters" >> helpmsg >> exitFailure
   Right e       → putStrLn e >> exitFailure
  return ()

fileMain ∷ FilePath → IO ()
fileMain path = do
  rules  ← parseFile path
  _      ← mapM print rules
  rules_ ← mapM (return . pΔ) rules
  _      ← mapM print rules_
  return ()
