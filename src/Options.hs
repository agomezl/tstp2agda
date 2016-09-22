
-- | Options module
-- Adapted from Apia and OnlineATPs

{-# LANGUAGE UnicodeSyntax     #-}


module Options
  ( options
  , OM
  , Options
    ( Options --Improve Haddock information.
    , optHelp
    , optInputFile
    , optModuleName
    , optOutputFile
    , optProofName
    , optVersion
    )
  , printUsage
  , processOptions
  ) where

import           Data.Char          (isDigit)
import           Data.List          (foldl', nub)
import qualified Data.Text          as T (pack)
import           System.Environment (getProgName)
import           Utils.PrettyPrint  (Doc, Pretty (pretty), squotes, (<>))


import System.Console.GetOpt
  ( ArgDescr(NoArg, ReqArg)
  , ArgOrder(ReturnInOrder)
  , getOpt
  , OptDescr(Option)
  , usageInfo
  )


-- | Program command-line options.
data Options = Options
  { optHelp           ∷ Bool
  , optInputFile      ∷ Maybe FilePath
  , optModuleName     ∷ String
  , optOutputFile     ∷ Maybe FilePath
  , optProofName      ∷ String
  , optVersion        ∷ Bool
  }

defaultOptions ∷ Options
defaultOptions = Options
  { optHelp           = False
  , optInputFile      = Nothing
  , optModuleName     = "Main"
  , optOutputFile     = Nothing
  , optProofName      = "proof"
  , optVersion        = False
  }

-- | 'Options' monad.
type OM = Options → Either Doc Options

helpOpt ∷ OM
helpOpt opts = Right opts { optHelp = True }

inputFileOpt ∷ FilePath → OM
inputFileOpt file opts =
  case optInputFile opts of
    Nothing → Right opts { optInputFile = Just file }
    Just _  → Left $ pretty "only one input file allowed"

moduleNameOpt ∷ String → OM
moduleNameOpt [] _ = Left $
  pretty "option " <> squotes "--module" <> pretty " requires an argument NAME"
moduleNameOpt mname opts = Right opts { optModuleName = mname}

outputFileOpt ∷ FilePath → OM
outputFileOpt file opts =
  case optOutputFile opts of
    Nothing → Right opts { optOutputFile = Just file }
    Just _  → Left $ pretty "only one input file allowed"

proofNameOpt ∷ String → OM
proofNameOpt [] _ = Left $
  pretty "option " <> squotes "--module" <> pretty " requires an argument NAME"
proofNameOpt pname opts = Right opts { optProofName = pname}

versionOpt ∷ OM
versionOpt opts = Right opts { optVersion = True }

-- | Description of the command-line 'Options'.
options ∷ [OptDescr OM]
options =
  [ Option ['f'] ["file","File"] (ReqArg inputFileOpt "FILE")
      "TSTP input file     (def: STDIN)"
  , Option ['h'] ["help"] (NoArg helpOpt)
      "prints help message"
  , Option ['m'] ["module-name"] (ReqArg moduleNameOpt "NAME")
      "module name         (def: Main)"
  , Option ['o'] ["output"] (ReqArg outputFileOpt "FILE")
      "output to file      (def: STDOUT)"
  , Option ['p'] ["proof-name"] (ReqArg proofNameOpt "NAME")
      "main proof name     (def: proof)"
  ]

usageHeader ∷ String → String
usageHeader prgName = "Usage: " ++ prgName ++ " [OPTIONS] FILE\n"

-- | Print usage information.
printUsage ∷ IO ()
printUsage = do
  progName ← getProgName
  putStrLn $ usageInfo (usageHeader progName) options

processOptionsHelper ∷ [String] → (FilePath → OM) → OM
processOptionsHelper argv f defaults =
  case getOpt (ReturnInOrder f) options argv of
    (o, _, [])   → foldl' (>>=) (return defaults) o
    (_, _, errs) → Left $ pretty $ unlines errs

-- -- | Processing the command-line 'Options'.
processOptions ∷ [String] → Either Doc Options
processOptions argv = processOptionsHelper argv inputFileOpt defaultOptions
