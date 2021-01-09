{-# Options -Wall -Wname-shadowing #-}
module Quadruples where

import qualified Data.Map as M
import Control.Monad.State

import qualified Frontend as F

type Label = String
data Location = Literal Integer | Str String | Reg String deriving Show

data BlockEnd
    = UnconditionalJump Label
    | ConditionalJump Condition Label Label
    | Return (Maybe Location)
    deriving Show
data Quadruple
    = Quadruple Location Op Location Location
    | Call Location String [Location]
    | GetVar Location F.Ident
    | AssignVar F.Ident Location
    | AssignLocal Location Int
    deriving Show
data Block = Block Label [Quadruple] BlockEnd deriving Show
data Condition = Loc Location | Rel RelOp Location Location deriving Show
data Op
    = Add
    | Sub
    | Mul
    | Div
    | Mod
    deriving Show
data RelOp
    = Lth
    | Le
    | Gth
    | Ge
    | Equ
    | Neq
    deriving Show

-- generation triple
type GenTriple = (Label, [Quadruple], [Block])

type StrEnv = M.Map F.Ident String

-- State (seed, map string -> location)
type QuadM = State (Int, StrEnv)

getNewTmpName :: QuadM Location
getNewTmpName = state (\(n, en) -> (Reg $ "_t" ++ show n, (n + 1, en)))

getNewTmpVar :: QuadM F.Ident
getNewTmpVar = state (\(n, en) -> ("_var" ++ show n, (n + 1, en)))

getNewLabel :: QuadM Label
getNewLabel = state (\(n, en) -> ("label_" ++ show n, (n + 1, en)))

-- get memory location for string literals
getStringName :: String -> QuadM Location
getStringName s = do
    (n, en) <- get
    case M.lookup s en of
        Nothing ->
            let name = "str" ++ show n in
            put (n + 1, M.insert s name en) >> return (Str name)
        Just name -> return (Str name)

getLoc :: F.Lvalue -> QuadM F.Ident
getLoc (F.VarRef _ _ ident) = return ident
getLoc (F.ClassAttr _ _ _ _) = undefined
getLoc (F.ArrRef _ _ _ _) = undefined

getQuadsProg :: F.Program -> ([([Block], [String])], StrEnv)
getQuadsProg (F.Program _ classDefs funDefs) =
    if not (null classDefs)
        then undefined
        else let (blocks, (_, strenv)) = runState (getQuadsFunDefs funDefs) (0, M.empty) in (blocks, strenv)

getQuadsFunDefs :: [F.FunDef] -> QuadM [([Block], [String])]
getQuadsFunDefs = mapM getQuadsFunDef

getQuadsFunDef :: F.FunDef -> QuadM ([Block], [String])
getQuadsFunDef (F.FunDef _ _ name args body) = do
    (lastLabel, quads, blocks) <- getQuadsBlock (name, [], []) body
    let argNames = map (\(_, _, argName) -> argName) args
    return (reverse $
        (Block lastLabel (reverse quads) (Return Nothing)) : blocks, argNames)

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
    let q2 = Quadruple tmpName' Add tmpName (Literal 1)
    let q3 = AssignVar addr tmpName'
    return $ (label, q3 : (q2 : (q1 : quads)), blocks)
getQuadsStmt (label, quads, blocks) (F.Decr _ lval) = do
    addr <- getLoc lval
    tmpName <- getNewTmpName
    tmpName' <- getNewTmpName
    let q1 = GetVar tmpName addr
    let q2 = Quadruple tmpName' Sub tmpName (Literal 1)
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
    thenLabel <- getNewLabel
    endLabel <- getNewLabel
    blocks <- getQuadsBExpr triple cond thenLabel endLabel
    (thenLabel', thenQuads, thenBlocks) <- getQuadsStmt
        (thenLabel, [], blocks)
        thenStmt
    let thenBlock = Block
            thenLabel'
            (reverse thenQuads)
            (UnconditionalJump endLabel)
    return (endLabel, [], thenBlock : thenBlocks)
getQuadsStmt triple (F.Cond _ cond thenStmt (Just elseStmt)) = do
    thenLabel <- getNewLabel
    elseLabel <- getNewLabel
    endLabel <- getNewLabel
    blocks <- getQuadsBExpr triple cond thenLabel elseLabel
    (thenLabel', thenQuads, thenBlocks) <- getQuadsStmt
        (thenLabel, [], blocks)
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
    blocksWithCond <- getQuadsBExpr (condLabel, [], block1 : blocks') cond bodyLabel endLabel
    return $ (endLabel, [], blocksWithCond)
getQuadsStmt triple (F.SExp _ expr) = do
    (triple', _) <- getQuadsExpr triple expr
    return triple'
getQuadsStmt (_, _, _) (F.For _ _ _ _) = undefined

getQuadsExpr :: GenTriple -> F.Expr -> QuadM (GenTriple, Location)
getQuadsExpr _ (F.ENewArr _ _ _ _) = undefined
getQuadsExpr _ (F.ENewObj _ _) = undefined
getQuadsExpr (label, quads, blocks) (F.EVar _ _ ident) = do
    reg <- getNewTmpName
    return ((label, (GetVar reg ident) : quads, blocks), reg)
getQuadsExpr triple (F.ELitInt _ n) = return (triple, Literal n)
getQuadsExpr triple (F.ELitBool _ True) = return (triple, Literal 1)
getQuadsExpr triple (F.ELitBool _ False) = return (triple, Literal 0)
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
    return ((label, (Quadruple res Sub (Literal 0) eVar) : quads, blocks), res)
getQuadsExpr triple (F.Not _ e) = do
    ((label, quads, blocks), eVar) <- getQuadsExpr triple e
    res <- getNewTmpName
    return ((label, (Quadruple res Sub (Literal 1) eVar) : quads, blocks), res)
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
getQuadsExpr triple e@(F.ERel _ _ _ _) = do
    res <- getNewTmpName
    labelTrue <- getNewLabel
    labelFalse <- getNewLabel
    blocks <- getQuadsBExpr triple e labelTrue labelFalse
    newLabel <- getNewLabel
    let blockTrue = Block
            labelTrue
            [AssignLocal res 1]
            (UnconditionalJump newLabel)
    let blockFalse = Block
            labelFalse
            [AssignLocal res 0]
            (UnconditionalJump newLabel)
    return ((newLabel, [], blockFalse : (blockTrue : blocks)), res)
getQuadsExpr triple e@(F.EBoolOp _ _ _ _) = do
    res <- getNewTmpName
    labelTrue <- getNewLabel
    labelFalse <- getNewLabel
    blocks <- getQuadsBExpr triple e labelTrue labelFalse
    newLabel <- getNewLabel
    let blockTrue = Block
            labelTrue
            [AssignLocal res 1]
            (UnconditionalJump newLabel)
    let blockFalse = Block
            labelFalse
            [AssignLocal res 0]
            (UnconditionalJump newLabel)
    return ((newLabel, [], blockFalse : (blockTrue : blocks)), res)

getQuadsBExpr :: GenTriple -> F.Expr -> Label -> Label -> QuadM [Block]
getQuadsBExpr _ (F.ENewArr _ _ _ _) _ _ = undefined
getQuadsBExpr _ (F.ENewObj _ _) _ _ = undefined
getQuadsBExpr triple e@(F.EVar F.Bool _ _) labelTrue labelFalse = do
    ((label, quads, blocks), reg) <- getQuadsExpr triple e
    let block = Block
            label
            (reverse quads)
            (ConditionalJump (Loc reg) labelTrue labelFalse)
    return $ block : blocks
getQuadsBExpr _ (F.EVar _ _ _) _ _ = undefined
getQuadsBExpr _ (F.ELitInt _ _) _ _ = undefined
getQuadsBExpr (label, quads, blocks) (F.ELitBool _ True ) labelTrue _ =
    let block = Block label (reverse quads) (UnconditionalJump labelTrue) in
    return $ block : blocks
getQuadsBExpr (label, quads, blocks) (F.ELitBool _ False) _ labelFalse =
    let block = Block label (reverse quads) (UnconditionalJump labelFalse) in
    return $ block : blocks
getQuadsBExpr _ (F.EString _ _) _ _ = undefined
getQuadsBExpr _ (F.ECoerce _ _) _ _ = undefined
getQuadsBExpr triple e@(F.EApp F.Bool _ _ _) labelTrue labelFalse = do
    ((label, quads, blocks), reg) <- getQuadsExpr triple e
    let block = Block
            label
            (reverse quads)
            (ConditionalJump (Loc reg) labelTrue labelFalse)
    return $ block : blocks
getQuadsBExpr _ (F.EApp _ _ _ _) _ _ = undefined
getQuadsBExpr _ (F.EClassMethod _ _ _ _ _) _ _ = undefined
getQuadsBExpr _ (F.EClassField _ _ _ _) _ _ = undefined
getQuadsBExpr _ (F.EArrAt _ _ _ _) _ _ = undefined
getQuadsBExpr _ (F.Neg _ _) _ _ = undefined
getQuadsBExpr triple (F.Not _ e) labelTrue labelFalse = getQuadsBExpr triple e labelFalse labelTrue
getQuadsBExpr _ (F.EIntOp _ _ _ _ _) _ _ = undefined
getQuadsBExpr triple (F.ERel _ e1 operand e2) labelTrue labelFalse = do
    (triple', reg1)  <- getQuadsExpr triple e1
    ((label, quads, blocks), reg2)  <- getQuadsExpr triple' e2
    let retVal op =
            let block = Block
                    label
                    (reverse quads)
                    (ConditionalJump (Rel op reg1 reg2) labelTrue labelFalse)
            in return $ block : blocks
    case operand of
        F.Lth -> retVal Lth
        F.Le -> retVal Le
        F.Gth -> retVal Gth
        F.Ge -> retVal Ge
        F.Equ -> retVal Equ
        F.Neq -> retVal Neq
getQuadsBExpr triple (F.EBoolOp _ e1 F.And e2) labelTrue labelFalse = do
    secondCondLabel <- getNewLabel
    blocks <- getQuadsBExpr triple e1 secondCondLabel labelFalse
    getQuadsBExpr (secondCondLabel, [], blocks) e2 labelTrue labelFalse
getQuadsBExpr triple (F.EBoolOp _ e1 F.Or e2) labelTrue labelFalse = do
    secondCondLabel <- getNewLabel
    blocks <- getQuadsBExpr triple e1 labelTrue secondCondLabel
    getQuadsBExpr (secondCondLabel, [], blocks) e2 labelTrue labelFalse

