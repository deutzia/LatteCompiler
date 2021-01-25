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
data Location
    = Literal Integer
    | Str String
    | Reg String
    deriving (Show, Eq, Ord)

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
    -- ReadPtr l0 l1 l2 == l0 = [l1 + l2 * size]
    | ReadPtr Location Location Location
    -- WritePtr l0 l1 l2 == [l0 + l1 * size] = l2
    | WritePtr Location Location Location
    deriving (Show, Eq, Ord)
data Block = Block Label [F.Ident] [Quadruple] BlockEnd deriving Show
data Condition = Loc Location | Rel RelOp Location Location deriving Show
data Op
    = Add
    | Sub
    | Mul
    | Div
    | Mod
    deriving (Show, Eq, Ord)
data RelOp
    = Lth
    | Le
    | Gth
    | Ge
    | Equ
    | Neq
    deriving (Show, Eq, Ord)

-- generation triple
type GenTriple = (Label, [F.Ident], [Quadruple], [Block])

type StrEnv = M.Map F.Ident String
-- map className ->
--      ((number of fields, map fieldName -> offset),
--          (number of methods, map methodName -> offset)
--          label of vtable)
type ClassEnv = M.Map F.Ident ((Integer, M.Map F.Ident Integer), (Integer, M.Map F.Ident Integer), Label)

-- State (seed, map string -> location, (function name, [function args]))
type QuadM = ReaderT ClassEnv (State (Int, StrEnv, (String, [String])))

getNewTmpVar :: QuadM String
getNewTmpVar = state (\(n, en, f) -> ("_var" ++ show n, (n + 1, en, f)))

getNewTmpName :: QuadM Location
getNewTmpName = state (\(n, en, f) -> (Reg $ "_t" ++ show n, (n + 1, en, f)))

getNewLabel :: QuadM Label
getNewLabel = state (\(n, en, f) -> ("label_" ++ show n, (n + 1, en, f)))

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
    (n, en, f) <- get
    case M.lookup s en of
        Nothing ->
            let name = "str" ++ show n in
            put (n + 1, M.insert s name en, f) >> return (Str name)
        Just name -> return (Str name)

dereference :: GenTriple -> F.Lvalue -> QuadM (GenTriple, Location)
dereference (label, vars, quads, blocks) (F.VarRef _ _ ident) = do
    reg <- getNewTmpName
    return ((label, vars, GetVar reg ident : quads, blocks), reg)
dereference triple (F.ArrRef _ _ lv expr) = do
    (triple', lv') <- dereference triple lv
    ((label, vars, quads, blocks), idx) <- getQuadsExpr triple' expr
    idxP1 <- getNewTmpName
    let add1 = Quadruple idxP1 Add idx (Literal 1)
    result <- getNewTmpName
    let qRead = ReadPtr result lv' idxP1
    return ((label, vars, qRead : (add1 : quads), blocks), result)
dereference triple (F.ClassAttr _ _ lv fieldIdent) = do
    ((label, vars, quads, blocks), lv') <- dereference triple lv
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
                                    return
                                        ((label,
                                            vars,
                                            q : quads, blocks),
                                            result)
        _ -> undefined

setVar :: GenTriple -> F.Lvalue -> Location -> QuadM GenTriple
setVar (label, vars, quads, blocks) (F.VarRef _ _ ident) rvalue =
    let q = AssignVar ident rvalue in
    return (label, vars, q : quads, blocks)
setVar triple (F.ArrRef _ _ lv expr) rvalue = do
    (triple', lv') <- dereference triple lv
    ((label, vars, quads, blocks), idx) <- getQuadsExpr triple' expr
    idxP1 <- getNewTmpName
    let add1 = Quadruple idxP1 Add idx (Literal 1)
    let q = WritePtr lv' idxP1 rvalue
    return (label, vars, q : add1 : quads, blocks)
setVar triple (F.ClassAttr _ _ lv fieldIdent) rvalue = do
    ((l, vs, qs, bs), lv') <- dereference triple lv
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
                                    return (l, vs, q : qs, bs)
        _ -> undefined

getWrittenVars :: F.Stmt -> [F.Ident]
getWrittenVars (F.Empty _) = []
getWrittenVars (F.BStmt _ (F.Block _ stmts)) = concatMap getWrittenVars stmts
getWrittenVars (F.Decl _ _ items) = map (\(F.Item _ ident _) -> ident) items
getWrittenVars (F.Ass _ lv _) = case lv of
    F.VarRef _ _ ident -> [ident]
    _ -> []
getWrittenVars (F.Ret _ _) = []
getWrittenVars (F.Cond _ _ thenStmt Nothing) = getWrittenVars thenStmt
getWrittenVars (F.Cond _ _ thenStmt (Just elseStmt)) =
    getWrittenVars thenStmt ++ getWrittenVars elseStmt
getWrittenVars (F.While _ _ stmt) = getWrittenVars stmt
getWrittenVars (F.SExp _ _) = []

getQuadsProg :: F.Program -> ([([Block], [String])], StrEnv, [(String, [String])])
getQuadsProg (F.Program _ classDefs funDefs) =
    let (classEnv, vtables) = createClassEnv classDefs in
    let
        funs = (id, funDefs) :
            map
                (\(F.ClassDef _ className _ _ methods) -> (renameMethod className, methods))
                classDefs
    in let
        (blocks, (_, strenv, _)) =
            runState
                (runReaderT (mapM getQuadsFunDefs funs) classEnv)
                (0, M.empty, ("", []))
    in (concat blocks, strenv, vtables)

getQuadsFunDefs :: (String -> String, [F.FunDef]) -> QuadM [([Block], [String])]
getQuadsFunDefs (prefix, fundefs) = do
    mapM (getQuadsFunDef prefix) fundefs

getQuadsFunDef :: (String -> String) -> F.FunDef -> QuadM ([Block], [String])
getQuadsFunDef prefix (F.FunDef _ _ name args body) =
    let argNames = map (\(_, _, argName) -> argName) args in
    do
    state (\(n, e, _) -> ((), (n, e, (prefix name, argNames))))
    (lastLabel, vars, quads, blocks) <-
            getQuadsBlock (prefix name, [], [], []) body
    return (reverse $
        Block lastLabel vars (reverse quads) (Return Nothing) : blocks,
            argNames)

getQuadsBlock :: GenTriple -> F.Block -> QuadM GenTriple
getQuadsBlock triple (F.Block _ stmts) = foldM getQuadsStmt triple stmts

getQuadsStmt :: GenTriple -> F.Stmt -> QuadM GenTriple
getQuadsStmt triple (F.Empty _) =
    return triple
getQuadsStmt (label, vars, quads, blocks) (F.BStmt _ b) = do
    nextLabel <- getNewLabel
    let block1 = Block label vars (reverse quads) (UnconditionalJump nextLabel)
    (label', vars', quads', blocks') <- getQuadsBlock
        (nextLabel, [], [], block1 : blocks) b
    nextLabel' <- getNewLabel
    let block2 = Block
            label'
            vars'
            (reverse quads')
            (UnconditionalJump nextLabel')
    return (nextLabel', [], [], block2 : blocks')
getQuadsStmt triple (F.Decl _ _ items) =
    foldM
        (\t (F.Item _ vName expr) -> do
            ((l, v, q, b), reg) <- getQuadsExpr t expr
            return (l, v, AssignVar vName reg : q, b)
        )
        triple
        items
getQuadsStmt triple (F.Ass _ lval expr) = do
    (triple', reg) <- getQuadsExpr triple expr
    setVar triple' lval reg
getQuadsStmt (label, vars, quads, blocks) (F.Ret _ Nothing) = do
    nextLabel <- getNewLabel
    let block = Block label vars (reverse quads) (Return Nothing)
    return (nextLabel, [], [], block : blocks)
getQuadsStmt triple (F.Ret _ (Just expr@(F.EApp _ _ fName args))) = do
    (_, _, (currentName, currentArgs)) <- get
    if fName == currentName
        then
            do
                ((label, vars, quads, blocks), args') <- foldM
                    (\(t, acc) arg -> do
                        (t', r) <- getQuadsExpr t arg
                        return (t', r : acc)
                        )
                    (triple, [])
                    args
                let writes = zipWith AssignVar currentArgs (reverse args')
                nextLabel <- getNewLabel
                let block = Block
                        label
                        vars
                        (reverse (writes ++ quads))
                        (UnconditionalJump (fName ++ ".internal"))
                return (nextLabel, [], [], block : blocks)
        else do
            nextLabel <- getNewLabel
            ((label, vars, quads, blocks), reg) <- getQuadsExpr triple expr
            let block = Block label vars (reverse quads) (Return (Just reg))
            return (nextLabel, [], [], block : blocks)
getQuadsStmt triple (F.Ret _ (Just expr)) = do
    nextLabel <- getNewLabel
    ((label, vars, quads, blocks), reg) <- getQuadsExpr triple expr
    let block = Block label vars (reverse quads) (Return (Just reg))
    return (nextLabel, [], [], block : blocks)
getQuadsStmt triple (F.Cond _ cond thenStmt Nothing) = do
    thenLabel <- getNewLabel
    endLabel <- getNewLabel
    blocks <- getQuadsBExpr triple cond thenLabel endLabel
    (thenLabel', thenVars, thenQuads, thenBlocks) <- getQuadsStmt
        (thenLabel, [], [], blocks)
        thenStmt
    let thenBlock = Block
            thenLabel'
            thenVars
            (reverse thenQuads)
            (UnconditionalJump endLabel)
    let vars = getWrittenVars thenStmt
    return (endLabel, vars, [], thenBlock : thenBlocks)
getQuadsStmt triple (F.Cond _ cond thenStmt (Just elseStmt)) = do
    thenLabel <- getNewLabel
    elseLabel <- getNewLabel
    endLabel <- getNewLabel
    blocks <- getQuadsBExpr triple cond thenLabel elseLabel
    (thenLabel', thenVars, thenQuads, thenBlocks) <- getQuadsStmt
        (thenLabel, [], [], blocks)
        thenStmt
    let thenBlock = Block
            thenLabel'
            thenVars
            (reverse thenQuads)
            (UnconditionalJump endLabel)
    (elseLabel', elseVars, elseQuads, elseBlocks) <- getQuadsStmt
        (elseLabel, [], [], thenBlock : thenBlocks)
        elseStmt
    let elseBlock = Block
            elseLabel'
            elseVars
            (reverse elseQuads)
            (UnconditionalJump endLabel)
    let vars = getWrittenVars thenStmt ++ getWrittenVars elseStmt
    return (endLabel, vars, [], elseBlock : elseBlocks)
getQuadsStmt (label, vars, quads, blocks) (F.While _ cond body) = do
    bodyLabel <- getNewLabel
    condLabel <- getNewLabel
    endLabel <- getNewLabel
    let vars' = getWrittenVars body
    let block0 = Block label vars (reverse quads) (UnconditionalJump condLabel)
    (bodyLabel', bodyVars, qs, blocks') <- getQuadsStmt
            (bodyLabel, vars', [], block0 : blocks) body
    let block1 = Block
            bodyLabel'
            bodyVars
            (reverse qs)
            (UnconditionalJump condLabel)
    blocksWithCond <-
        getQuadsBExpr
            (condLabel, vars', [], block1 : blocks')
            cond
            bodyLabel
            endLabel
    return (endLabel, vars', [], blocksWithCond)
getQuadsStmt triple (F.SExp _ expr) = do
    (triple', _) <- getQuadsExpr triple expr
    return triple'

getQuadsExpr :: GenTriple -> F.Expr -> QuadM (GenTriple, Location)
getQuadsExpr triple (F.ENewArr _ _ _ expr) = do
    ((label, vars, quads, blocks), size) <- getQuadsExpr triple expr
    arrAddr <- getNewTmpName
    sizeP1 <- getNewTmpName
    let add1 = Quadruple sizeP1 Add size (Literal 1)
    let call = Call arrAddr "allocate" [sizeP1]
    let writeSize = WritePtr arrAddr (Literal 0) size
    return ((label, vars, writeSize : (call : (add1 : quads)), blocks), arrAddr)
getQuadsExpr (label, vars, quads, blocks) (F.ENewObj _ t) = do
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
    return ((label, vars, qWrite : call : quads, blocks), res)
getQuadsExpr (label, vars, quads, blocks) (F.EVar _ _ ident) = do
    reg <- getNewTmpName
    return ((label, vars, GetVar reg ident : quads, blocks), reg)
getQuadsExpr triple (F.ELitInt _ n) = return (triple, Literal n)
getQuadsExpr triple (F.ELitBool _ True) = return (triple, Literal 1)
getQuadsExpr triple (F.ELitBool _ False) = return (triple, Literal 0)
getQuadsExpr triple (F.EString _ s) = do
    name <- getStringName s
    return (triple, name)
getQuadsExpr triple (F.ECoerce _ _) = return (triple, Literal 0)
getQuadsExpr triple (F.EApp _ _ fname args) = do
    ((label, vars, quads, blocks), args') <- foldM
        (\(t, acc) arg -> do
            (t', r) <- getQuadsExpr t arg
            return (t', r : acc)
            )
        (triple, [])
        args
    res <- getNewTmpName
    return
        ((label, vars, Call res fname (reverse args') : quads, blocks), res)
getQuadsExpr triple (F.EClassMethod _ _ classExpr methodIdent args) = do
    (triple', this) <- getQuadsExpr triple classExpr
    ((label, vars, quads, blocks), args') <- foldM
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
                            return ((label, vars, q2 : q1 : quads, blocks), res)
        _ -> undefined
getQuadsExpr triple (F.EClassField _ _ classExpr fieldIdent) =
    case F.typeOfExpr classExpr of
        F.Array _ -> if fieldIdent /= "length"
                then undefined
                else do
                    ((label, vars, quads, blocks), r) <-
                            getQuadsExpr triple classExpr
                    res <- getNewTmpName
                    let q = ReadPtr res r (Literal 0)
                    return ((label, vars, q : quads, blocks), res)
        F.Class classIdent -> do
                classEnv  <- ask
                case M.lookup classIdent classEnv of
                    Nothing -> undefined
                    Just ((_, fields), _, _) ->
                            case M.lookup fieldIdent fields of
                                Nothing -> undefined
                                Just offset -> do
                                    ((l, vs, qs, bs), r) <- getQuadsExpr
                                            triple
                                            classExpr
                                    res <- getNewTmpName
                                    let q = ReadPtr res r (Literal offset)
                                    return ((l, vs, q : qs, bs), res)
        _ -> undefined
getQuadsExpr triple (F.EArrAt _ _ arr idx) = do
    (triple', arr') <- getQuadsExpr triple arr
    ((label, vars, quads, blocks), idx') <- getQuadsExpr
        triple'
        (F.EIntOp F.Int Nothing idx F.Add (F.ELitInt Nothing 1))
    res <- getNewTmpName
    let q = ReadPtr res arr' idx'
    return ((label, vars, q : quads, blocks), res)
getQuadsExpr triple (F.Neg _ e) = do
    ((label, vars, quads, blocks), eVar) <- getQuadsExpr triple e
    res <- getNewTmpName
    return
        ((label, vars, Quadruple res Sub (Literal 0) eVar : quads, blocks),
            res)
getQuadsExpr triple (F.Not _ e) = do
    ((label, vars, quads, blocks), eVar) <- getQuadsExpr triple e
    res <- getNewTmpName
    return
        ((label, vars, Quadruple res Sub (Literal 1) eVar : quads, blocks),
            res)
getQuadsExpr triple (F.EIntOp t _ e1 operand e2) = do
    (triple1, v1) <- getQuadsExpr triple e1
    ((label, vars, quads, blocks), v2) <- getQuadsExpr triple1 e2
    res <- getNewTmpName
    let retVal op =
            return
                ((label, vars, Quadruple res op v1 v2 : quads, blocks), res)
    case operand of
        F.Mul -> retVal Mul
        F.Div -> retVal Div
        F.Mod -> retVal Mod
        F.Sub -> retVal Sub
        F.Add ->
            if t == F.Int
                then retVal Add
                else return
                    ((label,
                        vars,
                        Call res "_stradd" [v1, v2] : quads,
                        blocks),
                        res)
getQuadsExpr triple e@F.ERel {} = do
    var <- getNewTmpVar
    labelTrue <- getNewLabel
    labelFalse <- getNewLabel
    blocks <- getQuadsBExpr triple e labelTrue labelFalse
    newLabel <- getNewLabel
    let blockTrue = Block
            labelTrue
            []
            [AssignVar var (Literal 1)]
            (UnconditionalJump newLabel)
    let blockFalse = Block
            labelFalse
            []
            [AssignVar var (Literal 0)]
            (UnconditionalJump newLabel)
    res <- getNewTmpName
    let q = GetVar res var
    return ((newLabel, [var], [q], blockFalse : (blockTrue : blocks)), res)
getQuadsExpr triple e@F.EBoolOp {} = do
    var <- getNewTmpVar
    labelTrue <- getNewLabel
    labelFalse <- getNewLabel
    blocks <- getQuadsBExpr triple e labelTrue labelFalse
    newLabel <- getNewLabel
    let blockTrue = Block
            labelTrue
            []
            [AssignVar var (Literal 1)]
            (UnconditionalJump newLabel)
    let blockFalse = Block
            labelFalse
            []
            [AssignVar var (Literal 0)]
            (UnconditionalJump newLabel)
    res <- getNewTmpName
    let q = GetVar res var
    return ((newLabel, [var], [q], blockFalse : (blockTrue : blocks)), res)

getQuadsBExpr :: GenTriple -> F.Expr -> Label -> Label -> QuadM [Block]
getQuadsBExpr triple e@(F.EVar F.Bool _ _) labelTrue labelFalse = do
    ((label, vars, quads, blocks), reg) <- getQuadsExpr triple e
    let block = Block
            label
            vars
            (reverse quads)
            (ConditionalJump (Loc reg) labelTrue labelFalse)
    return $ block : blocks
getQuadsBExpr (label, vars, quads, blocks) (F.ELitBool _ True ) labelTrue _ =
    let
        block = Block label vars (reverse quads) (UnconditionalJump labelTrue)
    in
    return $ block : blocks
getQuadsBExpr (label, vars, quads, blocks) (F.ELitBool _ False) _ labelFalse =
    let
        block = Block label vars (reverse quads) (UnconditionalJump labelFalse)
    in
    return $ block : blocks
getQuadsBExpr triple (F.Not _ e) labelTrue labelFalse =
    getQuadsBExpr triple e labelFalse labelTrue
getQuadsBExpr triple (F.ERel _ e1 operand e2) labelTrue labelFalse = do
    (triple', reg1)  <- getQuadsExpr triple e1
    ((label, vars, quads, blocks), reg2)  <- getQuadsExpr triple' e2
    let retVal op =
            let block = Block
                    label
                    vars
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
    getQuadsBExpr (secondCondLabel, [], [], blocks) e2 labelTrue labelFalse
getQuadsBExpr triple (F.EBoolOp _ e1 F.Or e2) labelTrue labelFalse = do
    secondCondLabel <- getNewLabel
    blocks <- getQuadsBExpr triple e1 labelTrue secondCondLabel
    getQuadsBExpr (secondCondLabel, [], [], blocks) e2 labelTrue labelFalse
getQuadsBExpr triple expr labelTrue labelFalse = do
    ((label, vars, quads, blocks), reg) <- getQuadsExpr triple expr
    let block = Block
            label
            vars
            (reverse quads)
            (ConditionalJump (Loc reg) labelTrue labelFalse)
    return $ block : blocks
