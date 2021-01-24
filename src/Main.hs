{-# Options -Wall -Wname-shadowing #-}

module Main where

import qualified Data.Map as M
import System.Environment
import System.IO
import System.FilePath.Posix
import System.Exit
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import System.Process

import Parsing.ErrM
import Parsing.LexLatte
import Parsing.ParLatte
import Frontend
import Quadruples
import AsmBackend
import Optimizations

fileToS :: FilePath -> FilePath
fileToS fileName = dropExtension fileName ++ ".s"

fileToO :: FilePath -> FilePath
fileToO fileName = dropExtension fileName ++ ".o"

printErrorAndExit :: (Position, String) -> IO a
printErrorAndExit (Just (row, col), err) = do
    hPutStrLn stderr $ "ERROR\nstatic anaylsis error at line " ++ show row ++ ", column " ++ show col ++ ": " ++ err
    exitFailure
printErrorAndExit (Nothing, err) = do
    hPutStrLn stderr $ "ERROR\n" ++ err
    exitFailure

runFullCompile :: String -> IO ()
runFullCompile filename = do
    code <- readFile filename
    case pProgram (tokens code) of
        Ok program -> do
            let pass1Result = runExcept (evalStateT (runReaderT (pass1 program) (M.empty, M.empty, Void, Nothing)) (M.empty, 0, 0))
            case pass1Result of
                Left err -> printErrorAndExit err
                Right p@(Program _ _ _) -> do
                    hPutStrLn stderr $ "OK"
                    let outfilename = fileToS filename
                    let objectFilename = fileToO filename
                    let execFilename = dropExtension filename
                    writeFile outfilename ""
                    let outFun = appendFile outfilename
                    let (quads, strEnv, vtables) = getQuadsProg p
                    let quads' = optimizeQuads quads
                    generateAssembly outFun (quads', strEnv, vtables)
                    callCommand $ "nasm -g -f elf64 " ++ outfilename
                    callCommand $ "gcc " ++ objectFilename ++ " libs/runtime.o libs/calls.o -o " ++ execFilename
        Bad e -> printErrorAndExit (Nothing, e)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> hPutStrLn stderr "Error: no files to compile"
        files -> foldM (\() filename -> runFullCompile filename) () (reverse files)
