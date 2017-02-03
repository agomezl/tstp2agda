
-- | Options module
-- Adapted from Apia and OnlineATPs

{-# LANGUAGE UnicodeSyntax     #-}


module Options
  ( options
  , OM
  , Options
    ( Options --Improve Haddock information.
    , optEmbedding
    , optHelp
    , optInputFile
    , optOutputFile
    , optProofName
    , optVersion
    )
  , printUsage
  , processOptions
  ) where


import           Data.List          (foldl')
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
  { optEmbedding      ∷ Char
  , optHelp           ∷ Bool
  , optInputFile      ∷ Maybe FilePath
  , optOutputFile     ∷ Maybe FilePath
  , optProofName      ∷ String
  , optVersion        ∷ Bool
  }

defaultOptions ∷ Options
defaultOptions = Options
  { optEmbedding      = 's'
  , optHelp           = False
  , optInputFile      = Nothing
  , optOutputFile     = Nothing
  , optProofName      = "proof"
  , optVersion        = False
  }

-- | 'Options' monad.
type OM = Options → Either Doc Options

embeddingOpt ∷ String → OM
embeddingOpt "deep" opts    = Right opts { optEmbedding = 'd'}
embeddingOpt "shallow" opts = Right opts { optEmbedding = 's'}
embeddingOpt _ _ = Left $
  pretty "option " <> squotes "--embedding" <> pretty " requires an argument NAME"


helpOpt ∷ OM
helpOpt opts = Right opts { optHelp = True }

inputFileOpt ∷ FilePath → OM
inputFileOpt file opts =
  case optInputFile opts of
    Nothing → Right opts { optInputFile = Just file }
    Just _  → Left $ pretty "only one input file allowed"

outputFileOpt ∷ FilePath → OM
outputFileOpt file opts =
  case optOutputFile opts of
    Nothing → Right opts { optOutputFile = Just file }
    Just _  → Left $ pretty "only one input file allowed"

proofNameOpt ∷ String → OM
proofNameOpt [] _ = Left $
  pretty "option " <> squotes "--proof-name" <> pretty " requires an argument NAME"
proofNameOpt pname opts = Right opts { optProofName = pname}

versionOpt ∷ OM
versionOpt opts = Right opts { optVersion = True }

-- | Description of the command-line 'Options'.
options ∷ [OptDescr OM]
options =
  [ Option ['e'] ["embedding"] (ReqArg embeddingOpt "NAME")
      "shallow or deep (default: shallow)"
  , Option ['h'] ["help"] (NoArg helpOpt)
      "Prints help message"
  , Option ['o'] ["output"] (ReqArg outputFileOpt "FILE")
      "Output to file      (default: STDOUT)"
  , Option ['p'] ["proof-name"] (ReqArg proofNameOpt "NAME")
      "Main proof name     (default: proof)"
  , Option []    ["version"] (NoArg versionOpt)
      "Show version number"
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

-- | Processing the command-line 'Options'.
processOptions ∷ [String] → Either Doc Options
processOptions argv = processOptionsHelper argv inputFileOpt defaultOptions
