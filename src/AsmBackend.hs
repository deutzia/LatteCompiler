{-# Options -Wall -Wname-shadowing #-}
module AsmBackend where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import Control.Monad
import Control.Monad.Reader
import qualified Data.Function as F

import qualified Quadruples as Q

-- map from registers to offsets on the stack
type GenM = ReaderT (M.Map String Int) IO

prefix :: String
prefix =
    "bits 64\n" ++
    "default rel\n\n" ++
    "global _lat_main\n\n" ++
    "extern _stradd\n" ++
    "extern _strcmp\n" ++
    "extern _strncmp\n" ++
    "extern printInt\n" ++
    "extern printString\n" ++
    "extern readInt\n" ++
    "extern readString\n" ++
    "extern allocate\n" ++
    "extern error\n\n" ++
    "section .rodata\n"

wrapOut :: (String -> a) -> String -> a
wrapOut f = \s -> f $ "    " ++ s ++ "\n"

-- negated sign
nsgn :: Int -> String
nsgn x = if x >= 0 then "- " ++ show x else "+ " ++ show (-x)

fetchValReg :: (String -> GenM ()) -> String -> String -> GenM ()
fetchValReg outFun name reg = do
    regenv <- ask
    case M.lookup name regenv of
        Nothing -> undefined
        Just offset -> do
            outFun $ "lea r8, [rbp " ++ nsgn offset ++ "]"
            outFun $ "mov " ++ reg ++ ", [r8]"

fetchVal :: (String -> GenM ()) -> Q.Location -> String -> GenM ()
fetchVal outFun (Q.Reg name) reg = fetchValReg outFun name reg
fetchVal outFun (Q.Literal n) reg =
    outFun $ "mov " ++ reg ++ ", " ++ show n
fetchVal outFun (Q.Str name) reg =
    outFun $ "mov " ++ reg ++ ", " ++ name

writeValReg :: (String -> GenM ()) -> String -> String -> GenM ()
writeValReg outFun name reg = do
    regenv <- ask
    case M.lookup name regenv of
        Nothing -> undefined
        Just offset -> do
            outFun $ "lea r8, [rbp " ++ nsgn offset ++ "]"
            outFun $ "mov qword [r8], " ++ reg

writeVal :: (String -> GenM ()) -> Q.Location -> String -> GenM ()
writeVal outFun (Q.Reg name) reg = writeValReg outFun name reg
writeVal _ (Q.Literal _) _ = undefined
writeVal _ (Q.Str _) _ = undefined

generateData :: Q.StrEnv -> String
generateData strenv =
    let pairs = M.toList strenv in
    let
        strs = map
            (\(contents, name) ->
                if not (null contents)
                    then name ++ " db " ++ contents ++ ", 0\n"
                    else name ++ " db 0\n")
            pairs
    in
    concat strs

generateVtables :: (String -> IO ()) -> [(String, [String])] -> IO ()
generateVtables outFun vtables =
    foldM
        (\() (name, funs) -> do
            outFun $ name ++ " dq " ++ (L.intercalate ", " funs) ++ "\n"
        )
        ()
        vtables

generateAssembly :: (String -> IO ()) -> ([([Q.Block], [String])], Q.StrEnv, [(String, [String])]) -> IO ()
generateAssembly outFun (funs, strenv, vtables) = do
    outFun $ prefix ++ generateData strenv ++ "\nsection .text\n\n"
    generateVtables outFun vtables
    outFun "\n"
    foldM
        (\() (fun, args) ->
            let regs = getRegistersFun (fun, args) in
            let (maxOffset, regsEnv) = foldl (\(n, acc) reg -> (n + 8, M.insert reg n acc)) (8, M.empty) regs in
            let (_, regsEnv') = foldl(\(n, acc) reg -> (n + 8, M.insert reg (-n) acc)) (24, regsEnv) args in
            runReaderT (generateAssemblyFun (liftIO . outFun) maxOffset fun) regsEnv'
        )
        ()
        funs

generateAssemblyFun :: (String -> GenM ()) -> Int -> [Q.Block] -> GenM ()
generateAssemblyFun outFun offset blocks = do
    foldM_ (generateAssemblyBlock outFun) (offset, True)  blocks
    outFun "\n"

generateAssemblyBlock :: (String -> GenM ()) -> (Int, Bool) -> Q.Block -> GenM (Int, Bool)
generateAssemblyBlock outFun (offset, isFirst) (Q.Block label quads end) = do
    outFun $ label ++ ":\n"
    let wrappedOutFun = wrapOut outFun
    when isFirst (do
            wrappedOutFun "push rbp"
            wrappedOutFun "mov rbp, rsp"
            wrappedOutFun $ "sub rsp, " ++ show offset)
    foldM (generateAssemblyQuad wrappedOutFun) () quads
    generateAssemblyBEnd wrappedOutFun end
    return (offset, False)

generateAssemblyQuad :: (String -> GenM ()) -> () -> Q.Quadruple -> GenM ()
generateAssemblyQuad outFun () (Q.Quadruple r1 op r2 r3) = do
    fetchVal outFun r2 "rax"
    fetchVal outFun r3 "rsi"
    case op of
        Q.Add -> do
            outFun "add rax, rsi"
            writeVal outFun r1 "rax"
        Q.Sub -> do
            outFun "sub rax, rsi"
            writeVal outFun r1 "rax"
        Q.Mul -> do
            outFun "imul rax, rsi"
            writeVal outFun r1 "rax"
        Q.Div -> do
            outFun "cqo"
            outFun "idiv rsi"
            writeVal outFun r1 "rax"
        Q.Mod -> do
            outFun "cqo"
            outFun "idiv rsi"
            writeVal outFun r1 "rdx"
generateAssemblyQuad outFun () (Q.Call r1 name args) =
    let offset = length args + 1 in do
    outFun $ "sub rsp, " ++ show (offset * 8)
    foldM_
        (\ofs arg -> do
            fetchVal outFun arg "rax"
            outFun $ "lea r8, [rsp + " ++ show ofs ++ "]"
            outFun $ "mov [r8], rax"
            return (ofs + 8)
        )
        8
        args
    outFun $ "call " ++ name
    outFun $ "mov rax, [rsp]"
    outFun $ "add rsp, " ++ show (offset * 8)
    writeVal outFun r1 "rax"
generateAssemblyQuad outFun () (Q.CallLoc r1 (addr, callOfs) args) =
    let offset = length args + 1 in do
    outFun $ "sub rsp, " ++ show (offset * 8)
    foldM_
        (\ofs arg -> do
            fetchVal outFun arg "rax"
            outFun $ "lea r8, [rsp + " ++ show ofs ++ "]"
            outFun $ "mov [r8], rax"
            return (ofs + 8)
        )
        8
        args
    fetchVal outFun addr "rax"
    outFun $ "call [rax + " ++ show callOfs ++ " * 8]"
    outFun $ "mov rax, [rsp]"
    outFun $ "add rsp, " ++ show (offset * 8)
    writeVal outFun r1 "rax"
generateAssemblyQuad outFun () (Q.GetVar r1 r2) = do
    fetchValReg outFun r2 "rax"
    writeVal outFun r1 "rax"
generateAssemblyQuad outFun () (Q.AssignVar r1 r2) = do
    fetchVal outFun r2 "rax"
    writeValReg outFun r1 "rax"
generateAssemblyQuad outFun () (Q.AssignLocal reg (Q.Literal n)) =
    writeVal outFun reg (show n)
generateAssemblyQuad outFun () (Q.AssignLocal r1 r2) = do
    fetchVal outFun r2 "rax"
    writeVal outFun r1 "rax"
generateAssemblyQuad outFun () (Q.ReadPtr r1 r2 r3) = do
    fetchVal outFun r2 "rax"
    fetchVal outFun r3 "rsi"
    outFun $ "lea rdx, [rax + rsi * 8]"
    outFun $ "mov rax, [rdx]"
    writeVal outFun r1 "rax"
generateAssemblyQuad outFun () (Q.WritePtr r1 r2 r3) = do
    fetchVal outFun r1 "rax"
    fetchVal outFun r2 "rsi"
    fetchVal outFun r3 "rdx"
    outFun $ "lea rdi, [rax + rsi * 8]"
    outFun $ "mov [rdi], rdx"

generateAssemblyBEnd :: (String -> GenM ()) -> Q.BlockEnd -> GenM ()
generateAssemblyBEnd outFun (Q.UnconditionalJump label) =
    outFun $ "jmp " ++ label
generateAssemblyBEnd outFun (Q.ConditionalJump (Q.Loc cond) label1 label2) = do
    fetchVal outFun cond "rax"
    outFun $ "cmp rax, 0"
    outFun $ "je " ++ label2
    outFun $ "jmp " ++ label1
generateAssemblyBEnd outFun (Q.ConditionalJump (Q.Rel op loc1 loc2) label1 label2) = do
    fetchVal outFun loc1 "rax"
    fetchVal outFun loc2 "rdx"
    outFun "cmp rax, rdx"
    case op of
        Q.Lth -> outFun $ "jl " ++ label1
        Q.Le -> outFun $ "jle " ++ label1
        Q.Gth -> outFun $ "jg " ++ label1
        Q.Ge -> outFun $ "jge " ++ label1
        Q.Equ -> outFun $ "je " ++ label1
        Q.Neq -> outFun $ "jne " ++ label1
    outFun $ "jmp "  ++ label2
generateAssemblyBEnd outFun (Q.Return Nothing) = do
    outFun "mov rsp, rbp"
    outFun "pop rbp"
    outFun "ret"
generateAssemblyBEnd outFun (Q.Return (Just reg)) = do
    fetchVal outFun reg "rax"
    outFun "lea rdx, [rbp + 16]"
    outFun "mov [rdx], rax"
    outFun "mov rsp, rbp"
    outFun "pop rbp"
    outFun "ret"

getRegistersFun :: ([Q.Block], [String]) -> [String]
getRegistersFun (blocks, args) = S.toList $ (foldl getRegistersBlock S.empty blocks) S.\\ (S.fromList args)

getRegistersBlock :: S.Set String -> Q.Block -> S.Set String
getRegistersBlock regs (Q.Block _ quads bEnd) =
    (foldl getRegistersQuad (getRegistersBEnd regs bEnd)  quads)

getRegistersQuad :: S.Set String -> Q.Quadruple -> S.Set String
getRegistersQuad regs (Q.Quadruple r1 _ r2 r3) =
    (addLocationToRegisters r1 regs)
        F.& (addLocationToRegisters r2)
        F.& (addLocationToRegisters r3)
getRegistersQuad regs (Q.Call r _ rs) =
    foldr addLocationToRegisters (addLocationToRegisters r regs) rs
getRegistersQuad regs (Q.CallLoc r (r1, _) rs) =
    foldr
        addLocationToRegisters
        (addLocationToRegisters r (addLocationToRegisters r1 regs))
        rs
getRegistersQuad regs (Q.GetVar r1 r2) =
    S.insert r2 (addLocationToRegisters r1 regs)
getRegistersQuad regs (Q.AssignVar r1 r2) =
    S.insert r1 (addLocationToRegisters r2 regs)
getRegistersQuad regs (Q.AssignLocal r1 r2) =
    (addLocationToRegisters r1 regs)
        F.& (addLocationToRegisters r2)
getRegistersQuad regs (Q.WritePtr r1 r2 r3) =
    (addLocationToRegisters r1 regs)
        F.& (addLocationToRegisters r2)
        F.& (addLocationToRegisters r3)
getRegistersQuad regs (Q.ReadPtr r1 r2 r3) =
    (addLocationToRegisters r1 regs)
        F.& (addLocationToRegisters r2)
        F.& (addLocationToRegisters r3)

getRegistersBEnd :: S.Set String -> Q.BlockEnd -> S.Set String
getRegistersBEnd regs (Q.UnconditionalJump _) = regs
getRegistersBEnd regs (Q.ConditionalJump (Q.Loc reg) _ _) =
    addLocationToRegisters reg regs
getRegistersBEnd regs (Q.ConditionalJump (Q.Rel _ r1 r2) _ _) =
    addLocationToRegisters r1 (addLocationToRegisters r2 regs)
getRegistersBEnd regs (Q.Return Nothing) = regs
getRegistersBEnd regs (Q.Return (Just reg)) = addLocationToRegisters reg regs

addLocationToRegisters :: Q.Location -> S.Set String -> S.Set String
addLocationToRegisters (Q.Literal _) regs = regs
addLocationToRegisters (Q.Str _) regs = regs
addLocationToRegisters (Q.Reg name) regs = S.insert name regs

