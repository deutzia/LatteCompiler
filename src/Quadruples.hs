{-# Options -Wall -Wname-shadowing #-}
module Quadruples where

import qualified Data.Map as M
import Control.Monad.State

import qualified Frontend as F

type Label = String
type Register = String
data BlockEnd
    = UnconditionalJump Label
    | ConditionalJump Register Label Label
    | Return (Maybe Register)
    deriving Show
data Quadruple
    = Quadruple Register Op Register Register
    | Call Register String [Register]
    | GetVar Register F.Ident
    | AssignVar F.Ident Register
    deriving Show
data Block = Block Label [Quadruple] BlockEnd

data Op
    = Add
    | Sub
    | Mul
    | Div
    | Mod
    | Lth
    | Le
    | Gth
    | Ge
    | Equ
    | Neq
    deriving Show

-- generation triple
type GenTriple = (Label, [Quadruple], [Block])

type StrEnv = M.Map F.Ident Register

-- State (seed, map string -> location)
type QuadM = State (Int, StrEnv)

getNewTmpName :: QuadM Register
getNewTmpName = state (\(n, en) -> ("_t" ++ show n, (n + 1, en)))

getNewLabel :: QuadM Label
getNewLabel = state (\(n, en) -> ("label_" ++ show n, (n + 1, en)))

-- get memory location for string literals
getStringName :: String -> QuadM Register
getStringName s = do
    (n, en) <- get
    case M.lookup s en of
        Nothing ->
            let name = "[str" ++ show n ++ "]" in
            put (n + 1, M.insert s name en) >> return name
        Just name -> return name

getLoc :: F.Lvalue -> QuadM Register
getLoc (F.VarRef _ _ ident) = return ident
getLoc (F.ClassAttr _ _ _ _) = undefined
getLoc (F.ArrRef _ _ _ _) = undefined

getQuadsProg :: F.Program -> ([Block], StrEnv)
getQuadsProg (F.Program _ classDefs funDefs) =
    if not (null classDefs)
        then undefined
        else let (blocks, (_, strenv)) = runState (getQuadsFunDefs funDefs) (0, M.empty) in (reverse $ concat blocks, strenv)

getQuadsFunDefs :: [F.FunDef] -> QuadM [[Block]]
getQuadsFunDefs = mapM getQuadsFunDef

getQuadsFunDef :: F.FunDef -> QuadM [Block]
getQuadsFunDef (F.FunDef _ _ name _ body) = do
    (lastLabel, quads, blocks) <- getQuadsBlock (name, [], []) body
    return $ reverse $
        (Block lastLabel (reverse quads) (Return Nothing)) : blocks

getQuadsBlock :: GenTriple -> F.Block -> QuadM GenTriple
getQuadsBlock triple (F.Block _ stmts) = foldM getQuadsStmt triple stmts

getQuadsStmt :: GenTriple -> F.Stmt -> QuadM GenTriple
getQuadsStmt (label, quads, blocks) (F.Empty _) =
    return (label, quads, blocks)
getQuadsStmt (label, quads, blocks) (F.BStmt _ b) = do
    nextLabel <- getNewLabel
    let block1 = Block label (reverse quads) (UnconditionalJump nextLabel)
    (label', quads', blocks') <- getQuadsBlock
        (nextLabel, [], block1 : blocks) b
    nextLabel' <- getNewLabel
    let block2 = Block label' (reverse quads') (UnconditionalJump nextLabel')
    return (nextLabel', [], block2 : blocks')
getQuadsStmt triple (F.Decl _ _ items) =
    foldM
        (\t (F.Item _ vName expr) -> do
            ((l, q, b), reg) <- getQuadsExpr t expr
            return $ (l, (AssignVar vName reg) : q, b)
        )
        triple
        items
getQuadsStmt triple (F.Ass _ lval expr) = do
    ((label, quads, blocks), reg) <- getQuadsExpr triple expr
    addr <- getLoc lval
    return $ (label, (AssignVar addr reg) : quads, blocks)
getQuadsStmt (label, quads, blocks) (F.Incr _ lval) = do
    addr <- getLoc lval
    tmpName <- getNewTmpName
    tmpName' <- getNewTmpName
    let q1 = GetVar tmpName addr
    let q2 = Quadruple tmpName' Add tmpName "1"
    let q3 = AssignVar addr tmpName'
    return $ (label, q3 : (q2 : (q1 : quads)), blocks)
getQuadsStmt (label, quads, blocks) (F.Decr _ lval) = do
    addr <- getLoc lval
    tmpName <- getNewTmpName
    tmpName' <- getNewTmpName
    let q1 = GetVar tmpName addr
    let q2 = Quadruple tmpName' Sub tmpName "1"
    let q3 = AssignVar addr tmpName'
    return $ (label, q3 : (q2 : (q1 : quads)), blocks)
getQuadsStmt (label, quads, blocks) (F.Ret _ Nothing) = do
    nextLabel <- getNewLabel
    return $
        (nextLabel, [], (Block label (reverse quads) (Return Nothing)) : blocks)
getQuadsStmt triple (F.Ret _ (Just expr)) = do
    nextLabel <- getNewLabel
    ((label, quads, blocks), reg) <- getQuadsExpr triple expr
    let block = Block label (reverse quads) (Return (Just reg))
    return $ (nextLabel, [], block : blocks)
getQuadsStmt triple (F.Cond _ cond thenStmt Nothing) = do
    ((label, quads, blocks), cond') <- getQuadsExpr triple cond
    thenLabel <- getNewLabel
    endLabel <- getNewLabel
    let thisBlock = Block
            label
            (reverse quads)
            (ConditionalJump cond' thenLabel endLabel)
    (thenLabel', thenQuads, thenBlocks) <- getQuadsStmt
        (thenLabel, [], (thisBlock : blocks))
        thenStmt
    let thenBlock = Block
            thenLabel'
            (reverse thenQuads)
            (UnconditionalJump endLabel)
    return (endLabel, [], thenBlock : thenBlocks)
getQuadsStmt triple (F.Cond _ cond thenStmt (Just elseStmt)) = do
    ((label, quads, blocks), cond') <- getQuadsExpr triple cond
    thenLabel <- getNewLabel
    elseLabel <- getNewLabel
    endLabel <- getNewLabel
    let thisBlock = Block
            label
            (reverse quads)
            (ConditionalJump cond' thenLabel endLabel)
    (thenLabel', thenQuads, thenBlocks) <- getQuadsStmt
        (thenLabel, [], (thisBlock : blocks))
        thenStmt
    let thenBlock = Block
            thenLabel'
            (reverse thenQuads)
            (UnconditionalJump endLabel)
    (elseLabel', elseQuads, elseBlocks) <- getQuadsStmt
        (elseLabel, [], thenBlock : thenBlocks)
        elseStmt
    let elseBlock = Block
            elseLabel'
            (reverse elseQuads)
            (UnconditionalJump endLabel)
    return $ (endLabel, [], elseBlock : elseBlocks)
getQuadsStmt (label, quads, blocks) (F.While _ cond body) = do
    bodyLabel <- getNewLabel
    condLabel <- getNewLabel
    endLabel <- getNewLabel
    let block0 = Block label (reverse quads) (UnconditionalJump condLabel)
    (bodyLabel', qs, blocks') <- getQuadsStmt
            (bodyLabel, [], block0 : blocks) body
    let block1 = Block bodyLabel' (reverse qs) (UnconditionalJump condLabel)
    ((condLabel', condQuads, condBlocks), cond') <- getQuadsExpr
        (condLabel, [], block1 : blocks')
        cond
    let block2 = Block
            condLabel'
            (reverse condQuads)
            (ConditionalJump cond' bodyLabel endLabel)
    return $ (endLabel, [], block2 : condBlocks)
getQuadsStmt triple (F.SExp _ expr) = do
    (triple', _) <- getQuadsExpr triple expr
    return triple'
getQuadsStmt (_, _, _) (F.For _ _ _ _) = undefined

getQuadsExpr :: GenTriple -> F.Expr -> QuadM (GenTriple, Register)
getQuadsExpr _ (F.ENewArr _ _ _ _) = undefined
getQuadsExpr _ (F.ENewObj _ _) = undefined
getQuadsExpr (label, quads, blocks) (F.EVar _ _ ident) = do
    reg <- getNewTmpName
    return ((label, (GetVar reg ident) : quads, blocks), reg)
getQuadsExpr triple (F.ELitInt _ n) = return (triple, show n)
getQuadsExpr triple (F.ELitBool _ True) = return (triple, "1")
getQuadsExpr triple (F.ELitBool _ False) = return (triple, "0")
getQuadsExpr triple (F.EString _ s) = do
    name <- getStringName s
    return (triple, name)
getQuadsExpr _ (F.ECoerce _ _) = undefined
getQuadsExpr triple (F.EApp _ _ fname args) = do
    ((label, quads, blocks), args') <- foldM
        (\(t, acc) arg -> do
            (t', r) <- getQuadsExpr t arg
            return (t', r : acc)
            )
        (triple, [])
        args
    res <- getNewTmpName
    return ((label, (Call res fname (reverse args')) : quads, blocks), res)
getQuadsExpr _ (F.EClassMethod _ _ _ _ _) = undefined
getQuadsExpr _ (F.EClassField _ _ _ _) = undefined
getQuadsExpr _ (F.EArrAt _ _ _ _) = undefined
getQuadsExpr triple (F.Neg _ e) = do
    ((label, quads, blocks), eVar) <- getQuadsExpr triple e
    res <- getNewTmpName
    return ((label, (Quadruple res Sub "0" eVar) : quads, blocks), res)
getQuadsExpr triple (F.Not _ e) = do
    ((label, quads, blocks), eVar) <- getQuadsExpr triple e
    res <- getNewTmpName
    return ((label, (Quadruple res Sub "1" eVar) : quads, blocks), res)
getQuadsExpr triple (F.EIntOp t _ e1 operand e2) = do
    (triple1, v1) <- getQuadsExpr triple e1
    ((label, quads, blocks), v2) <- getQuadsExpr triple1 e2
    res <- getNewTmpName
    let retVal op =
            return ((label, (Quadruple res op v1 v2) : quads, blocks), res)
    case operand of
        F.Mul -> retVal Mul
        F.Div -> retVal Div
        F.Mod -> retVal Mod
        F.Sub -> retVal Sub
        F.Add ->
            if t == F.Int
                then retVal Add
                else return
                    ((label, (Call res "_stradd" [v1, v2]) : quads, blocks),
                        res)
getQuadsExpr triple (F.ERel _ e1 operand e2) = do
    (triple1, v1) <- getQuadsExpr triple e1
    ((label, quads, blocks), v2) <- getQuadsExpr triple1 e2
    res <- getNewTmpName
    let retVal op =
            return ((label, (Quadruple res op v1 v2) : quads, blocks), res)
    case operand of
        F.Lth -> retVal Lth
        F.Le -> retVal Le
        F.Gth -> retVal Gth
        F.Ge -> retVal Ge
        F.Equ ->
            case F.typeOfExpr e1 of
                F.Int -> retVal Equ
                F.Bool -> retVal Equ
                F.String_ -> return
                    ((label, (Call res "_strcmp" [v1, v2]) : quads, blocks),
                        res)
                _ -> undefined
        F.Neq ->
            case F.typeOfExpr e1 of
                F.Int -> retVal Neq
                F.Bool -> retVal Neq
                F.String_ -> return
                    ((label, (Call res "_strncmp" [v1, v2]) : quads, blocks),
                        res)
                _ -> undefined
getQuadsExpr triple (F.EBoolOp _ e1 F.And e2) = do
    ((label, quads, blocks), reg1) <- getQuadsExpr triple e1
    secondCondLabel <- getNewLabel
    knownFalseLabel <- getNewLabel
    endLabel <- getNewLabel
    varName <- getNewTmpName
    res <- getNewTmpName
    let block0 = Block
            label
            (reverse quads)
            (ConditionalJump reg1 secondCondLabel knownFalseLabel)
    let block1 = Block
            knownFalseLabel
            [AssignVar varName "0"]
            (UnconditionalJump endLabel)
    ((label', quads', blocks'), reg2) <- getQuadsExpr
        (secondCondLabel, [], block1 : (block0 : blocks)) e2
    let block2 = Block
            label'
            (reverse (AssignVar varName reg2 : quads'))
            (UnconditionalJump endLabel)
    return ((endLabel, [GetVar res varName], block2 : blocks'), res)
getQuadsExpr triple (F.EBoolOp _ e1 F.Or e2) = do
    ((label, quads, blocks), reg1) <- getQuadsExpr triple e1
    secondCondLabel <- getNewLabel
    knownTrueLabel <- getNewLabel
    endLabel <- getNewLabel
    varName <- getNewTmpName
    res <- getNewTmpName
    let block0 = Block
            label
            (reverse quads)
            (ConditionalJump reg1 knownTrueLabel secondCondLabel)
    let block1 = Block
            knownTrueLabel
            [AssignVar varName "1"]
            (UnconditionalJump endLabel)
    ((label', quads', blocks'), reg2) <- getQuadsExpr
        (secondCondLabel, [], block1 : (block0 : blocks)) e2
    let block2 = Block
            label'
            (reverse (AssignVar varName reg2 : quads'))
            (UnconditionalJump endLabel)
    return ((endLabel, [GetVar res varName], block2 : blocks'), res)

