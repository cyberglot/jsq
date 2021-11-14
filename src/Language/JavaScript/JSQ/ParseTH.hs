module Language.JavaScript.JSQ.ParseTH (parseHSExp) where

import Language.Haskell.Meta.Parse ( parseExp )
import qualified Language.Haskell.TH as TH

parseHSExp :: String -> Either String TH.Exp
parseHSExp = parseExp
