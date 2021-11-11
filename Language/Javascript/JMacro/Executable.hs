{-# LANGUAGE GADTs, RankNTypes #-}

module Main where

import Text.PrettyPrint.Leijen.Text (hPutDoc)
import Control.Applicative ()
import Control.Monad ( when )
import Language.JavaScript.JMacro.Base
    ( JMGadt(JMGStat),
      JMacro(jtoGADT, jfromGADT),
      Ident(StrI),
      JStat(DeclStat),
      composOp,
      scopify,
      renderJs )
import Language.JavaScript.JMacro.QQ ( parseJM )
import System.Environment ()
import System.Console.ParseArgs
    ( argDataOptional,
      getArgStdio,
      gotArg,
      parseArgsIO,
      usageError,
      IOMode(WriteMode, ReadMode),
      Arg(Arg),
      ArgsComplete(ArgsComplete),
      Argtype(ArgtypeString) )
import System.IO
    ( stderr, IOMode(WriteMode, ReadMode), hGetContents, hPrint )

main :: IO ()
main = do
   args <- parseArgsIO ArgsComplete
           [Arg "Scope" (Just 's') (Just "scope") Nothing "Enforce block scoping through global variable renames.",
            Arg "Help" (Just 'h') (Just "help") Nothing "",
            Arg "Infile"  Nothing Nothing (argDataOptional "Input file"  ArgtypeString) "Input file",
            Arg "Outfile" Nothing Nothing (argDataOptional "Output file" ArgtypeString) "Output file"]
   when (gotArg args "Help") $ usageError args "Transforms jmacro code into valid javascript."
   let s = gotArg args "Scope"
   infile <- getArgStdio args "Infile" ReadMode
   outfile <- getArgStdio args "Outfile" WriteMode
   either (hPrint stderr) (hPutDoc outfile) . parseIt s =<< hGetContents infile
  where
    parseIt True  = onRight (renderJs . scopify)  . parseJM
    parseIt False = onRight (renderJs . fixIdent) . parseJM
    onRight :: (a -> b) -> Either c a -> Either c b
    onRight f (Right x) = Right (f x)
    onRight _ (Left x) = Left x

    fixIdent x = jfromGADT $ composOp go (jtoGADT x) :: JStat
        where
          go :: forall a. JMGadt a -> JMGadt a
          go v = case v of
                       (JMGStat (DeclStat (StrI ('!':'!':i')) t)) -> JMGStat (DeclStat (StrI i') t)
                       (JMGStat (DeclStat (StrI ('!':i')) t)) -> JMGStat (DeclStat (StrI i') t)
                       _ -> composOp go v
