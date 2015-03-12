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

data Flag = File String |
            Help
          deriving(Eq,Ord,Show)

options ∷ [OptDescr Flag]
options =
  [Option ['f'] ["file","File"] (ReqArg File "File")
   "TPTP input file",
   Option ['h','?'] ["help"] (NoArg Help)
   "prints help message"
  ]


compileOpts ∷ [String] → Either [Flag] String
compileOpts argv =
  case getOpt RequireOrder options argv of
    (o,[],[])   -> Left o
    ([],[f],[]) -> Left [File f]
    (_,_,[])    -> Right $ "bad parameters\n" ++ usageInfo header options
    (_,_,e)     -> Right $ concat e ++ usageInfo header options
  where header = "Usage: tstp2agda [-f] file"

helpmsg ∷ IO ()
helpmsg = putStrLn $ usageInfo msg options
  where
    msg = "Usage: tstp2agda [-f] file"
