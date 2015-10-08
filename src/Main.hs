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
import Args               (compileOpts,helpmsg,Flag(..))
import TSTP.Parser        (parseTSTP)
import TSTP.Lexer         (alexScanTokens)
import Data.TSTP

import System.Exit (exitFailure)

parse :: String -> [F]
parse = parseTSTP . map snd . alexScanTokens

parseFile :: FilePath -> IO [F]
parseFile x = parse `fmap` readFile x

main :: IO ()
main = do
  args <- getArgs
  case compileOpts args of
   Left [Args.File f] → fileMain f
   Left [Help]   → helpmsg
   Left _        → putStrLn "Bad parameters" >> helpmsg >> exitFailure
   Right e       → putStrLn e >> exitFailure
  return ()

fileMain ∷ FilePath → IO ()
fileMain path = do
  rules  ← parseFile path
  mapM_ print rules
