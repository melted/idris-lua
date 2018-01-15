module Main where

import Idris.Core.TT
import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.Options
import Idris.REPL
import Idris.Main

import IRTS.Compiler
import IRTS.CodegenLua

import System.Environment
import System.Exit

import Paths_idris_lua

data Opts = Opts { inputs :: [FilePath],
                   output :: FilePath }

showUsage = do putStrLn "Usage: idris-codegen-lua <ibc-files> [-o <output-file>]"
               exitSuccess

getOpts :: IO Opts
getOpts = do xs <- getArgs
             return $ process (Opts [] "a.lua") xs
  where
    process opts ("-o":o:xs) = process (opts { output = o }) xs
    process opts (x:xs) = process (opts { inputs = x:inputs opts }) xs
    process opts [] = opts

build :: Opts -> Idris ()
build opts = do elabPrims
                loadInputs (inputs opts) Nothing
                mainProg <- elabMain
                ir <- compile (Via IBCFormat "lua") (output opts) (Just mainProg)
                runIO $ codegenLua ir

main :: IO ()
main = do opts <- getOpts
          if null (inputs opts)
             then showUsage
             else runMain (build opts)
