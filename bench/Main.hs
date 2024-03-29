{-# LANGUAGE QuasiQuotes #-}

module Main where

import Criterion.Main
import Language.JavaScript.JSQ
import Text.PrettyPrint.Leijen.Text (renderPretty, renderCompact, displayT)

main = defaultMain [pretty, compact]

pretty = bench "pretty" $ nf (displayT . renderPretty 0.4 100 . renderJs) jmPrelude

compact = bench "compact" $ nf (displayT . renderCompact . renderJs) jmPrelude
