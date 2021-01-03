{-# Options -Wall -Wname-shadowing #-}
module Quadruples where

import qualified Data.Map as M
import Control.Monad.State

import qualified Frontend as F

type Label = String
type Register = String -- name of the variable / temporary variable
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
    | And
    | Or
    | Lth
    | Le
    | Gth
    | Ge
    | Equ
    | Neq
    deriving Show

-- State (seed, map string -> location)
type QuadM = State (Int, M.Map F.Ident Register)

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

negateIntRel :: F.IntRel -> F.IntRel
negateIntRel F.Lth = F.Ge
negateIntRel F.Le = F.Gth
negateIntRel F.Gth = F.Le
negateIntRel F.Ge = F.Lth
negateIntRel F.Equ = F.Neq
negateIntRel F.Neq = F.Equ

negateBoolOp :: F.BoolOp -> F.BoolOp
negateBoolOp F.Or = F.And
negateBoolOp F.And = F.Or

getLoc :: F.Lvalue -> QuadM Register
getLoc (F.VarRef _ _ ident) = return ident
getLoc (F.ClassAttr _ _ _ _) = undefined
getLoc (F.ArrRef _ _ _ _) = undefined

getQuadsProg :: F.Program -> [Block]
getQuadsProg (F.Program _ classDefs funDefs) =
    if not (null classDefs)
        then undefined
        -- TODO don't discard state
        else concat $ map (\fundef -> evalState (getQuadsFunDef fundef) (0, M.empty)) funDefs

getQuadsFunDef :: F.FunDef -> QuadM [Block]
getQuadsFunDef (F.FunDef _ _ name _ body) = do
    (lastLabel, quads, blocks) <- getQuadsBlock (name, [], []) body
    return $ reverse $
        (Block lastLabel (reverse quads) (Return Nothing)) : blocks

getQuadsBlock :: (Label, [Quadruple], [Block]) -> F.Block -> QuadM (Label, [Quadruple], [Block])
getQuadsBlock triple (F.Block _ stmts) = foldM getQuadsStmt triple stmts

getQuadsStmt :: (Label, [Quadruple], [Block]) -> F.Stmt -> QuadM (Label, [Quadruple], [Block])
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
getQuadsStmt (label, quads, blocks) (F.Decl _ _ items) = do
    quads' <- foldM
        (\qs (F.Item _ vName expr) -> do
            (qs', reg) <- getQuadsExpr expr
            return $ (AssignVar vName reg) : (qs' ++ qs)
        )
        quads
        items
    return (label, quads', blocks)
getQuadsStmt (label, quads, blocks) (F.Ass _ lval expr) = do
    (qs, reg) <- getQuadsExpr expr
    addr <- getLoc lval
    return $ (label, (AssignVar addr reg) : (qs ++ quads), blocks)
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
getQuadsStmt (label, quads, blocks) (F.Ret _ (Just expr)) = do
    nextLabel <- getNewLabel
    (qs, reg) <- getQuadsExpr expr
    let block = Block label (reverse $ qs ++ quads) (Return (Just reg))
    return $ (nextLabel, [], block : blocks)
getQuadsStmt (label, quads, blocks) (F.Cond _ cond thenStmt Nothing) = do
    (condQuads, cond') <- getQuadsExpr cond
    thenLabel <- getNewLabel
    endLabel <- getNewLabel
    let thisBlock = Block
            label
            (reverse $ condQuads ++ quads)
            (ConditionalJump cond' thenLabel endLabel)
    (thenLabel', thenQuads, thenBlocks) <- getQuadsStmt
        (thenLabel, [], (thisBlock : blocks))
        thenStmt
    let thenBlock = Block
            thenLabel'
            (reverse thenQuads)
            (UnconditionalJump endLabel)
    return (endLabel, [], thenBlock : thenBlocks)
getQuadsStmt
    (label, quads, blocks)
    (F.Cond _ cond thenStmt (Just elseStmt)) = do
    (condQuads, cond') <- getQuadsExpr cond
    thenLabel <- getNewLabel
    elseLabel <- getNewLabel
    endLabel <- getNewLabel
    let thisBlock = Block
            label
            (reverse $ condQuads ++ quads)
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
    (condQs, cond') <- getQuadsExpr cond
    let block2 = Block
            condLabel
            (reverse condQs)
            (ConditionalJump cond' bodyLabel endLabel)
    return $ (endLabel, [], block2 : (block1 : blocks'))
getQuadsStmt (label, quads, blocks) (F.SExp _ expr) = do
    (qs, _) <- getQuadsExpr expr
    return $ (label, qs ++ quads, blocks)
getQuadsStmt (_, _, _) (F.For _ _ _ _) = undefined

getQuadsExpr :: F.Expr -> QuadM ([Quadruple], Register)
getQuadsExpr (F.ENewArr _ _ _ _) = undefined
getQuadsExpr (F.ENewObj _ _) = undefined
getQuadsExpr (F.EVar _ _ ident) = do
    reg <- getNewTmpName
    return ([GetVar reg ident], reg)
getQuadsExpr (F.ELitInt _ n) = return ([], show n)
getQuadsExpr (F.ELitBool _ True) = return ([], "1")
getQuadsExpr (F.ELitBool _ False) = return ([], "0")
getQuadsExpr (F.EString _ s) = do
    name <- getStringName s
    return ([], name)
getQuadsExpr (F.ECoerce _ _) = undefined
getQuadsExpr (F.EApp _ _ fname args) = do
    args' <- mapM getQuadsExpr args
    let quads = concatMap fst args'
    res <- getNewTmpName
    return ((Call res fname (map snd args')) : quads, res)
getQuadsExpr (F.EClassMethod _ _ _ _ _) = undefined
getQuadsExpr (F.EClassField _ _ _ _) = undefined
getQuadsExpr (F.EArrAt _ _ _ _) = undefined
getQuadsExpr (F.Neg _ e) = do
    (quads, eVar) <- getQuadsExpr e
    res <- getNewTmpName
    return ((Quadruple res Sub "0" eVar) : quads, res)
getQuadsExpr (F.Not _ e) = do
    (quads, eVar) <- getQuadsExpr e
    res <- getNewTmpName
    return ((Quadruple res Sub "1" eVar) : quads, res)
getQuadsExpr (F.EIntOp t _ e1 op e2) = do
    (q1, v1) <- getQuadsExpr e1
    (q2, v2) <- getQuadsExpr e2
    res <- getNewTmpName
    case op of
        F.Mul -> return ((Quadruple res Mul v1 v2) : (q2 ++ q1), res)
        F.Div -> return ((Quadruple res Div v1 v2) : (q2 ++ q1), res)
        F.Mod -> return ((Quadruple res Mod v1 v2) : (q2 ++ q1), res)
        F.Sub -> return ((Quadruple res Sub v1 v2) : (q2 ++ q1), res)
        F.Add ->
            if t == F.Int
                then return ((Quadruple res Mul v1 v2) : (q2 ++ q1), res)
                else return ((Call res "_stradd" [v1, v2]) : (q2 ++ q1), res)
getQuadsExpr (F.ERel _ e1 op e2) = do
    (q1, v1) <- getQuadsExpr e1
    (q2, v2) <- getQuadsExpr e2
    res <- getNewTmpName
    case op of
        F.Lth -> return ((Quadruple res Lth v1 v2) : (q2 ++ q1), res)
        F.Le -> return ((Quadruple res Le v1 v2) : (q2 ++ q1), res)
        F.Gth -> return ((Quadruple res Gth v1 v2) : (q2 ++ q1), res)
        F.Ge -> return ((Quadruple res Ge v1 v2) : (q2 ++ q1), res)
        F.Equ ->
            case F.typeOfExpr e1 of
                F.Int -> return ((Quadruple res Equ v1 v2) : (q2 ++ q1), res)
                F.Bool -> return ((Quadruple res Equ v1 v2) : (q2 ++ q1), res)
                F.String_ -> return
                    ((Call res "_strcmp" [v1, v2]) : (q2 ++ q1), res)
                _ -> undefined
        F.Neq ->
            case F.typeOfExpr e1 of
                F.Int -> return ((Quadruple res Neq v1 v2) : (q2 ++ q1), res)
                F.Bool -> return ((Quadruple res Neq v1 v2) : (q2 ++ q1), res)
                F.String_ -> return
                    ((Call res "_strncmp" [v1, v2]) : (q2 ++ q1), res)
                _ -> undefined
getQuadsExpr (F.EBoolOp _ e1 op e2) = do
    (q1, v1) <- getQuadsExpr e1
    (q2, v2) <- getQuadsExpr e2
    res <- getNewTmpName
    case op of
        F.Or -> return ((Quadruple res Or v1 v2) : (q2 ++ q1), res)
        F.And -> return ((Quadruple res And v1 v2) : (q2 ++ q1), res)

