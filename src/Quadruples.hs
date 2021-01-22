{-# Options -Wall -Wname-shadowing #-}
module Quadruples where

import qualified Data.Map as M
import qualified Data.Graph as G
import qualified Data.Maybe as Maybe
import qualified Data.List as L
import Control.Monad.State
import Control.Monad.Reader

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
    -- CallLoc res (l0, l1) [args] == res = call [l0 + l1 * size] [args]
    | CallLoc Location (Location, Integer) [Location]
    | GetVar Location F.Ident
    | AssignVar F.Ident Location
    | AssignLocal Location Location
    -- ReadPtr l0 l1 l2 == l0 = [l1 + l2 * size]
    | ReadPtr Location Location Location
    -- WritePtr l0 l1 l2 == [l0 + l1 * size] = l2
    | WritePtr Location Location Location
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
-- map className ->
--      ((number of fields, map fieldName -> offset),
--          (number of methods, map methodName -> offset)
--          label of vtable)
type ClassEnv = M.Map F.Ident ((Integer, M.Map F.Ident Integer), (Integer, M.Map F.Ident Integer), Label)

-- State (seed, map string -> location)
type QuadM = ReaderT ClassEnv (State (Int, StrEnv))

getNewTmpName :: QuadM Location
getNewTmpName = state (\(n, en) -> (Reg $ "_t" ++ show n, (n + 1, en)))

getNewTmpVar :: QuadM F.Ident
getNewTmpVar = state (\(n, en) -> ("_var" ++ show n, (n + 1, en)))

getNewLabel :: QuadM Label
getNewLabel = state (\(n, en) -> ("label_" ++ show n, (n + 1, en)))

vtable :: String -> String
vtable className = "_lat_vtable_" ++ className

renameMethod :: String -> String -> String
renameMethod className methodName = "_lat_" ++ className ++ "." ++ methodName

createClassEnv :: [F.ClassDef] -> (ClassEnv, [(String, [String])])
createClassEnv classes =
    let
        getFields (n, acc) (F.Field _ _ ident) = (n + 1, M.insert ident n acc)
    in let
        graph = map (\c@(F.ClassDef _ className maybeParent _ _) ->
                (c, className, Maybe.maybeToList maybeParent))
            classes
    in let
        sortedClasses =
                concatMap G.flattenSCC $ G.stronglyConnComp graph
    in let
        (classEnv, vtables) = foldl
            (\(acc, vtm) (F.ClassDef _ className maybeParent fields methods) ->
                let
                    getMethods (n, m_acc, m_vtm) (F.FunDef _ _ ident _ _) =
                        case M.lookup ident m_acc of
                            Nothing ->
                                (n + 1,
                                    M.insert ident n m_acc,
                                    M.insert
                                        n
                                        (renameMethod className ident)
                                        m_vtm)
                            Just ofs ->
                                (n,
                                    m_acc,
                                    M.insert
                                        ofs
                                        (renameMethod className ident)
                                        m_vtm)
                in case maybeParent of
                    Nothing ->
                        let
                            (n, cenvMod, vtb) =
                                foldl getMethods (0, M.empty, M.empty) methods
                        in (M.insert
                                className
                                (foldl getFields (1, M.empty) fields,
                                    (n, cenvMod),
                                    vtable className)
                                acc,
                            M.insert className vtb vtm)
                    Just parent ->
                        case (M.lookup parent acc, M.lookup parent vtm) of
                            (Just (pFields, (pOfs, pMethods), _), Just pVtb) ->
                                let (n, cenvMod, vtb) =
                                        foldl
                                            getMethods
                                            (pOfs, pMethods, pVtb)
                                            methods
                                in (M.insert
                                        className
                                        (foldl getFields pFields fields,
                                            (n, cenvMod),
                                            vtable className)
                                        acc,
                                    M.insert className vtb vtm)
                            _ -> undefined
            )
            (M.empty, M.empty)
            sortedClasses
    in let
        vtables' =
            map
                (\(k, v) -> (vtable k, map snd $ L.sort $ M.toList v))
                (M.toList vtables)
    in (classEnv, vtables')

-- get memory location for string literals
getStringName :: String -> QuadM Location
getStringName s = do
    (n, en) <- get
    case M.lookup s en of
        Nothing ->
            let name = "str" ++ show n in
            put (n + 1, M.insert s name en) >> return (Str name)
        Just name -> return (Str name)

dereference :: GenTriple -> F.Lvalue -> QuadM (GenTriple, Location)
dereference (label, quads, blocks) (F.VarRef _ _ ident) = do
    reg <- getNewTmpName
    return ((label, (GetVar reg ident) : quads, blocks), reg)
dereference triple (F.ArrRef _ _ lv expr) = do
    (triple', lv') <- dereference triple lv
    ((label, quads, blocks), idx) <- getQuadsExpr triple' expr
    idxP1 <- getNewTmpName
    let add1 = Quadruple idxP1 Add idx (Literal 1)
    result <- getNewTmpName
    let qRead = ReadPtr result lv' idxP1
    return ((label, qRead : (add1 : quads), blocks), result)
dereference triple (F.ClassAttr _ _ lv fieldIdent) = do
    ((label, quads, blocks), lv') <- dereference triple lv
    case F.typeOfLvalue lv of
        F.Class classIdent -> do
                classEnv <- ask
                case M.lookup classIdent classEnv of
                    Nothing -> undefined
                    Just ((_, fields), _, _) ->
                            case M.lookup fieldIdent fields of
                                Nothing -> undefined
                                Just offset -> do
                                    result <- getNewTmpName
                                    let q = ReadPtr result lv' (Literal offset)
                                    return ((label, q : quads, blocks), result)
        _ -> undefined

setVar :: GenTriple -> F.Lvalue -> Location -> QuadM GenTriple
setVar (label, quads, blocks) (F.VarRef _ _ ident) rvalue =
    let q = AssignVar ident rvalue in
    return (label, q : quads, blocks)
setVar triple (F.ArrRef _ _ lv expr) rvalue = do
    (triple', lv') <- dereference triple lv
    ((label, quads, blocks), idx) <- getQuadsExpr triple' expr
    idxP1 <- getNewTmpName
    let add1 = Quadruple idxP1 Add idx (Literal 1)
    let q = WritePtr lv' idxP1 rvalue
    return (label, q : add1 : quads, blocks)
setVar triple (F.ClassAttr _ _ lv fieldIdent) rvalue = do
    ((l, qs, bs), lv') <- dereference triple lv
    case F.typeOfLvalue lv of
        F.Class classIdent -> do
                classEnv  <- ask
                case M.lookup classIdent classEnv of
                    Nothing -> undefined
                    Just ((_, fields), _, _) ->
                            case M.lookup fieldIdent fields of
                                Nothing -> undefined
                                Just offset -> do
                                    let q = WritePtr lv' (Literal offset) rvalue
                                    return (l, q : qs, bs)
        _ -> undefined

getQuadsProg :: F.Program -> ([([Block], [String])], StrEnv, [(String, [String])])
getQuadsProg (F.Program _ classDefs funDefs) =
    let (classEnv, vtables) = createClassEnv classDefs in
    let
        funs = (id, funDefs) :
            (map
                (\(F.ClassDef _ className _ _ methods) -> (renameMethod className, methods))
                classDefs)
    in let
        (blocks, (_, strenv)) =
            runState
                (runReaderT (mapM getQuadsFunDefs funs) classEnv)
                (0, M.empty)
    in (concat blocks, strenv, vtables)

getQuadsFunDefs :: ((String -> String), [F.FunDef]) -> QuadM [([Block], [String])]
getQuadsFunDefs (prefix, fundefs) = do
--    traceM $ show (prefix "", fundefs)
    mapM (getQuadsFunDef prefix) fundefs

getQuadsFunDef :: (String -> String) -> F.FunDef -> QuadM ([Block], [String])
getQuadsFunDef prefix (F.FunDef _ _ name args body) = do
    (lastLabel, quads, blocks) <- getQuadsBlock (prefix name, [], []) body
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
    (triple', reg) <- getQuadsExpr triple expr
    setVar triple' lval reg
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

getQuadsExpr :: GenTriple -> F.Expr -> QuadM (GenTriple, Location)
getQuadsExpr triple (F.ENewArr _ _ _ expr) = do
    ((label, quads, blocks), size) <- getQuadsExpr triple expr
    arrAddr <- getNewTmpName
    sizeP1 <- getNewTmpName
    let add1 = Quadruple sizeP1 Add size (Literal 1)
    let call = Call arrAddr "allocate" [sizeP1]
    let writeSize = WritePtr arrAddr (Literal 0) size
    return ((label, writeSize : (call : (add1 : quads)), blocks), arrAddr)
getQuadsExpr (label, quads, blocks) (F.ENewObj _ t) = do
    (size, vt) <- case t of
        F.Class classIdent -> do
            classEnv <- ask
            case M.lookup classIdent classEnv of
                Nothing -> undefined
                Just ((s, _), _, vtab) -> return (s, vtab)
        _ -> undefined
    res <- getNewTmpName
    let call = Call res "allocate" [Literal size]
    let qWrite = WritePtr res (Literal 0) (Str vt)
    return ((label, qWrite : call : quads, blocks), res)
getQuadsExpr (label, quads, blocks) (F.EVar _ _ ident) = do
    reg <- getNewTmpName
    return ((label, (GetVar reg ident) : quads, blocks), reg)
getQuadsExpr triple (F.ELitInt _ n) = return (triple, Literal n)
getQuadsExpr triple (F.ELitBool _ True) = return (triple, Literal 1)
getQuadsExpr triple (F.ELitBool _ False) = return (triple, Literal 0)
getQuadsExpr triple (F.EString _ s) = do
    name <- getStringName s
    return (triple, name)
getQuadsExpr triple (F.ECoerce _ _) = return (triple, Literal 0)
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
getQuadsExpr triple (F.EClassMethod _ _ classExpr methodIdent args) = do
    (triple', this) <- getQuadsExpr triple classExpr
    ((label, quads, blocks), args') <- foldM
        (\(t, acc) arg -> do
            (t', r) <- getQuadsExpr t arg
            return (t', r : acc)
            )
        (triple', [])
        args
    case F.typeOfExpr classExpr of
        F.Class classIdent -> do
            classEnv <- ask
            case M.lookup classIdent classEnv of
                Nothing -> undefined
                Just (_, (_, methods), _) -> do
                    case M.lookup methodIdent methods of
                        Nothing -> undefined
                        Just offset -> do
                            tmp <- getNewTmpName
                            res <- getNewTmpName
                            let q1 = ReadPtr tmp this (Literal 0)
                            let q2 = CallLoc
                                    res
                                    (tmp, offset)
                                    (this : reverse args')
                            return ((label, q2 : q1 : quads, blocks), res)
        _ -> undefined
getQuadsExpr triple (F.EClassField _ _ classExpr fieldIdent) =
    case F.typeOfExpr classExpr of
        F.Array _ -> if fieldIdent /= "length"
                then undefined
                else do
                    ((label, quads, blocks), r) <- getQuadsExpr triple classExpr
                    res <- getNewTmpName
                    let q = ReadPtr res r (Literal 0)
                    return ((label, q : quads, blocks), res)
        F.Class classIdent -> do
                classEnv  <- ask
                case M.lookup classIdent classEnv of
                    Nothing -> undefined
                    Just ((_, fields), _, _) ->
                            case M.lookup fieldIdent fields of
                                Nothing -> undefined
                                Just offset -> do
                                    ((l, qs, bs), r) <- getQuadsExpr
                                            triple
                                            classExpr
                                    res <- getNewTmpName
                                    let q = ReadPtr res r (Literal offset)
                                    return ((l, q : qs, bs), res)
        _ -> undefined
getQuadsExpr triple (F.EArrAt _ _ arr idx) = do
    (triple', arr') <- getQuadsExpr triple arr
    ((label, quads, blocks), idx') <- getQuadsExpr
        triple'
        (F.EIntOp F.Int Nothing idx F.Add (F.ELitInt Nothing 1))
    res <- getNewTmpName
    let q = ReadPtr res arr' idx'
    return ((label, q : quads, blocks), res)
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
            [AssignLocal res (Literal 1)]
            (UnconditionalJump newLabel)
    let blockFalse = Block
            labelFalse
            [AssignLocal res (Literal 0)]
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
            [AssignLocal res (Literal 1)]
            (UnconditionalJump newLabel)
    let blockFalse = Block
            labelFalse
            [AssignLocal res (Literal 0)]
            (UnconditionalJump newLabel)
    return ((newLabel, [], blockFalse : (blockTrue : blocks)), res)

getQuadsBExpr :: GenTriple -> F.Expr -> Label -> Label -> QuadM [Block]
getQuadsBExpr triple e@(F.EVar F.Bool _ _) labelTrue labelFalse = do
    ((label, quads, blocks), reg) <- getQuadsExpr triple e
    let block = Block
            label
            (reverse quads)
            (ConditionalJump (Loc reg) labelTrue labelFalse)
    return $ block : blocks
getQuadsBExpr (label, quads, blocks) (F.ELitBool _ True ) labelTrue _ =
    let block = Block label (reverse quads) (UnconditionalJump labelTrue) in
    return $ block : blocks
getQuadsBExpr (label, quads, blocks) (F.ELitBool _ False) _ labelFalse =
    let block = Block label (reverse quads) (UnconditionalJump labelFalse) in
    return $ block : blocks
getQuadsBExpr triple (F.Not _ e) labelTrue labelFalse =
    getQuadsBExpr triple e labelFalse labelTrue
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
getQuadsBExpr triple expr labelTrue labelFalse = do
    ((label, quads, blocks), reg) <- getQuadsExpr triple expr
    let block = Block
            label
            (reverse quads)
            (ConditionalJump (Loc reg) labelTrue labelFalse)
    return $ block : blocks
