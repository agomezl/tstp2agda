
-- | Args module

{-# LANGUAGE UnicodeSyntax #-}

module Args where

import           System.Console.GetOpt (ArgDescr (..), ArgOrder (..),
                                        OptDescr (..), getOpt, usageInfo)

data Flag = Help
          | InFile     String
          | ModuleName String
          | OutFile    String
          | ProofName  String
          deriving(Eq, Ord, Show)


data Conf = Conf
  { inputFile  ∷ Maybe String
  , moduleName ∷ String
  , outputFile ∷ Maybe String
  , printhelp  ∷ Bool
  , proofName  ∷ String
  }

options ∷ [OptDescr Flag]
options =
  [ Option ['f'] ["file","File"] (ReqArg InFile "File")
      "TSTP input file     (def: STDIN)"
  , Option ['h'] ["help"] (NoArg Help)
      "prints help message"
  , Option ['m'] ["module-name"] (ReqArg ModuleName "Name")
      "module name         (def: Main)"
  , Option ['o'] ["output"] (ReqArg OutFile "File")
      "output to file      (def: STDOUT)"
  , Option ['p'] ["proof-name"] (ReqArg ProofName "Name")
      "main proof name     (def: proof)"
  ]

defaultConf ∷ Conf
defaultConf = Conf Nothing Nothing False "Main" "proof"

compileOpts ∷ [String] → Either Conf String
compileOpts argv =
  case getOpt RequireOrder options argv of
    ([],[] ,[]) → Left    defaultConf
    (o ,[] ,[]) → Left  $ parseOpts o defaultConf
    ([],[f],[]) → Left  $ defaultConf { inputFile = Just f }
    (_ ,_  ,[]) → Right $ "bad parameters\n" ++ usageInfo header options
    (_ ,_  ,e ) → Right $ concat e ++ usageInfo header options
  where header = "Usage: tstp2agda [OPTIONS]"

parseOpts ∷ [Flag] → Conf → Conf
parseOpts [] conf     = conf
parseOpts (x:xs) conf = parseOpts xs $ update x
    where
      update (Help     )    = conf { printhelp  = True }
      update (InFile  f)    = conf { inputFile  = Just f }
      update (ModuleName f) = conf { moduleName = f }
      update (OutFile f)    = conf { outputFile = Just f }
      update (ProofName  f) = conf { proofName  = f }

helpmsg ∷ IO ()
helpmsg = putStrLn $ usageInfo msg options
  where
    msg = "Usage: tstp2agda [OPTIONS]"
