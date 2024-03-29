{-# LANGUAGE RankNTypes
           , GADTs
#-}

module Main where

import Control.Applicative ()
import Control.Monad (when)
import Language.JavaScript.JSQ.Base
  ( Ident (StrI),
    JSQ (jfromGADT, jtoGADT),
    JSQGadt (JSQGStat),
    JStat (DeclStat),
    composOp,
    renderJs,
    scopify,
  )
import Language.JavaScript.JSQ.QQ (parseJSQ)
import System.Console.ParseArgs
  ( Arg (Arg),
    ArgsComplete (ArgsComplete),
    Argtype (ArgtypeString),
    IOMode (ReadMode, WriteMode),
    argDataOptional,
    getArgStdio,
    gotArg,
    parseArgsIO,
    usageError,
  )
import System.Environment ()
import System.IO
  ( IOMode (ReadMode, WriteMode),
    hGetContents,
    hPrint,
    stderr,
  )
import Text.PrettyPrint.Leijen.Text (hPutDoc)

main :: IO ()
main = do
  args <-
    parseArgsIO
      ArgsComplete
      [ Arg "Scope" (Just 's') (Just "scope") Nothing "Enforce block scoping through global variable renames.",
        Arg "Help"  (Just 'h') (Just "help")  Nothing "",
        Arg "Infile"  Nothing Nothing (argDataOptional "Input file"  ArgtypeString) "Input file",
        Arg "Outfile" Nothing Nothing (argDataOptional "Output file" ArgtypeString) "Output file"
      ]
  when (gotArg args "Help") $ usageError args "Transforms jsq code into valid javascript."
  let s = gotArg args "Scope"
  infile <- getArgStdio args "Infile" ReadMode
  outfile <- getArgStdio args "Outfile" WriteMode
  either (hPrint stderr) (hPutDoc outfile) . parseIt s =<< hGetContents infile
  where
    parseIt True = onRight (renderJs . scopify) . parseJSQ
    parseIt False = onRight (renderJs . fixIdent) . parseJSQ
    onRight :: (a -> b) -> Either c a -> Either c b
    onRight f (Right x) = Right (f x)
    onRight _ (Left x) = Left x

    fixIdent x = jfromGADT $ composOp go (jtoGADT x) :: JStat
      where
        go :: forall a. JSQGadt a -> JSQGadt a
        go v = case v of
          (JSQGStat (DeclStat (StrI ('!' : '!' : i')) t)) -> JSQGStat (DeclStat (StrI i') t)
          (JSQGStat (DeclStat (StrI ('!' : i')) t)) -> JSQGStat (DeclStat (StrI i') t)
          _ -> composOp go v
