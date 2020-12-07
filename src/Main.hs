{-# Options -Wall -Wname-shadowing #-}

module Main where

import qualified Data.Map as M
import System.Environment
import System.IO
import System.FilePath.Posix
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import Parsing.ErrM
import Parsing.LexLatte
import Parsing.ParLatte
import Frontend

fileToS :: FilePath -> FilePath
fileToS fileName = dropExtension fileName ++ ".s"

runFullCompile :: String -> IO ()
runFullCompile filename = do
    code <- readFile filename
    case pProgram (tokens code) of
        Ok program -> do
            let outFilename = fileToS
            let pass1Result = runExcept (evalStateT (runReaderT (pass1 program) (M.empty, M.empty)) (M.empty, 0))
            case pass1Result of
                Left (Just (col, row), err) -> hPutStrLn stderr $ "Error at column " ++ show col ++ " row " ++ show row ++ ": " ++ err
                Left (Nothing, err) -> hPutStrLn stderr $ "Error at unknown location: " ++ err
                Right (Program pos _ _) ->  putStrLn $ "Ok " ++ show pos
        Bad e -> hPutStrLn stderr e

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> hPutStrLn stderr "Error: no files to compile"
        files -> foldM (\() filename -> runFullCompile filename) () (reverse files)
