{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Args
-- Author : Alejandro Gómez Londoño
-- Date   : Wed Mar 11 23:32:30 2015
-- Description : Argument management
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------
module Args where

import System.Console.GetOpt (OptDescr(..),
                              ArgDescr(..),
                              ArgOrder(..),
                              getOpt,
                              usageInfo)

data Flag = InFile String  |
            OutFile String |
            Help
          deriving(Eq,Ord,Show)

data Conf = Conf {
      inputFile  ∷ Maybe String,
      outputFile ∷ Maybe String,
      printhelp  ∷ Bool
    }

options ∷ [OptDescr Flag]
options =
  [Option ['f'] ["file","File"] (ReqArg InFile "File")
   "TSTP input file",
   Option ['o'] ["output"] (ReqArg OutFile "File")
   "output to file",
   Option ['h','?'] ["help"] (NoArg Help)
   "prints help message"
  ]

defaultConf ∷ Conf
defaultConf = Conf Nothing Nothing False

compileOpts ∷ [String] → Either Conf String
compileOpts argv =
  case getOpt RequireOrder options argv of
    ([],[] ,[]) → Left    defaultConf
    (o ,[] ,[]) → Left  $ parseOpts o defaultConf
    ([],[f],[]) → Left  $ defaultConf { inputFile = Just f }
    (_ ,_  ,[]) → Right $ "bad parameters\n" ++ usageInfo header options
    (_ ,_  ,e ) → Right $ concat e ++ usageInfo header options
  where header = "Usage: tstp2agda [-f] file"

parseOpts ∷ [Flag] → Conf → Conf
parseOpts [] conf     = conf
parseOpts (x:xs) conf = parseOpts xs $ update x
    where update (InFile  f) = conf { inputFile  = Just f }
          update (OutFile f) = conf { outputFile = Just f }
          update (Help     ) = conf { printhelp  = True }

helpmsg ∷ IO ()
helpmsg = putStrLn $ usageInfo msg options
  where
    msg = "Usage: tstp2agda [-f] file"
