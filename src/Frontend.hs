{-# Options -Wall -Wname-shadowing #-}

module Frontend where

import qualified Data.Map as M
import qualified Data.Graph as G
import qualified Data.Set as S
import qualified Data.Maybe as Maybe
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Util

import qualified Parsing.AbsLatte as Abs

type Position = Maybe (Int, Int)
type Ident = String
data Type
    = Int
    | Bool
    | String_
    | Void
    | Class Ident
    | Array Type
    deriving Eq

instance Show Type where
    show Int = "integer"
    show Bool = "boolean"
    show String_ = "string"
    show Void = "void"
    show (Class ident) = ident
    show (Array t) = show t ++ "[]"

data Program = Program Position [ClassDef] [FunDef] deriving Show
data ClassDef = ClassDef Position Ident (Maybe Ident) [Field] [FunDef]
    deriving Show
data Field = Field Position Type Ident deriving Show
data FunDef = FunDef Position Type Ident [Arg] Block deriving Show
type Arg = (Position, Type, Ident)
data Block = Block Position [Stmt] deriving Show
data Stmt
    = Empty Position
    | BStmt Position Block
    | Decl Position Type [Item]
    | Ass Position Lvalue Expr
    | Ret Position (Maybe Expr)
    | Cond Position Expr Stmt (Maybe Stmt)
    | While Position Expr Stmt
    | SExp Position Expr
    deriving Show
data Item = Item Position Ident Expr deriving Show
-- position and type are kept for every nonobvious expression and lvalue
data Expr
    = ENewArr Type Position Type Expr
    | ENewObj Position Type
    | EVar Type Position Ident
    | ELitInt Position Integer
    | ELitBool Position Bool
    | EString Position String
    | ECoerce Position Type
    | EApp Type Position Ident [Expr]
    | EClassMethod Type Position Expr Ident [Expr]
    | EClassField Type Position Expr Ident
    | EArrAt Type Position Expr Expr
    | Neg Position Expr
    | Not Position Expr
    | EIntOp Type Position Expr IntOp Expr
    | ERel Position Expr IntRel Expr
    | EBoolOp Position Expr BoolOp Expr
    deriving Show
data Lvalue
    = VarRef Type Position Ident
    | ClassAttr Type Position Lvalue Ident
    | ArrRef Type Position Lvalue Expr
    deriving Show

data IntOp = Mul | Div | Add | Sub | Mod deriving Show
data IntRel = Lth | Le | Gth | Ge | Equ | Neq deriving Show
data BoolOp = Or | And deriving Show

type Depth = Integer
type Venv = M.Map Ident (Type, Depth, Ident) -- variable env
type Fenv = M.Map Ident (Type, [Type], Ident) -- function env
-- classident -> (fieldname -> type), (methodname -> (rettype, argtypes)), parent
type Cenv =
    M.Map Ident (M.Map Ident Type, M.Map Ident (Type, [Type], Ident), Maybe Ident)
-- ReaderT (fenv, cenv, type returned by current fuction, class we're in)
-- StateT (venv, depth of blocks, name seed)
type Pass1M =
    ReaderT
        (Fenv, Cenv, Type, Maybe Ident)
        (StateT (Venv, Depth, Int) (Except (Position, String)))

data ReturnState = RSUnknown | RSNever | RSYes deriving Eq

createVarName :: Pass1M Ident
createVarName =
    state (\(venv, d, seed) -> ("var" ++ show seed, (venv, d, seed + 1)))

checkReturnBlock :: Block -> ReturnState
checkReturnBlock (Block _ stmts) =
    foldl (\res stmt ->
        if res == RSNever || res == RSYes
        then res
        else checkReturnStmt stmt) RSUnknown stmts

checkReturnStmt :: Stmt -> ReturnState
checkReturnStmt stmt =
    case stmt of
        Empty _ -> RSUnknown
        BStmt _ block -> checkReturnBlock block
        Decl{} -> RSUnknown
        Ass{} -> RSUnknown
        Ret{} -> RSYes
        Cond _ _ s1 (Just s2) ->
            let
                res1 = checkReturnStmt s1
                res2 = checkReturnStmt s2
            in
            if res1 == res2
                then res1
                else
                    if (res1 == RSYes && res2 == RSNever)
                    || (res1 == RSNever && res2 == RSYes)
                        then RSYes
                        else RSUnknown
        Cond{} -> RSUnknown
        -- allow using while (true) without return
        While _ (ELitBool _ True) _ -> RSNever
        While{} -> RSUnknown
        SExp _ (EApp _ _ "error" _) -> RSNever
        SExp{} -> RSUnknown

pass1BuiltinType :: Abs.BuiltinType Position -> Type
pass1BuiltinType (Abs.Int _) = Int
pass1BuiltinType (Abs.Str _) = String_
pass1BuiltinType (Abs.Bool _) = Bool
pass1BuiltinType (Abs.Void _) = Void

pass1ClassType :: String -> Position -> Pass1M Type
pass1ClassType ident pos = do
    (_, cenv, _, _) <- ask
    if M.member ident cenv
        then return (Class ident)
        else throwError (pos, "Undeclared type: " ++ ident)

pass1ArrayType :: Abs.ArrayType Position -> Pass1M Type
pass1ArrayType (Abs.BuiltinArr _ type_) =
    return $ Array (pass1BuiltinType type_)
pass1ArrayType (Abs.UserArr pos (Abs.Ident ident)) =
    Array <$> pass1ClassType ident pos

pass1Type :: Abs.Type Position -> Pass1M Type
pass1Type (Abs.BltinType _ t) = return (pass1BuiltinType t)
pass1Type (Abs.ArrType _ t) = pass1ArrayType t
pass1Type (Abs.UserType pos (Abs.Ident ident)) = pass1ClassType ident pos

-- first arg is maybe class name to add `self` to args
pass1FunDef :: (Maybe Ident) -> Abs.FunDef Position -> Pass1M FunDef
pass1FunDef maybeClass (Abs.FunDef pos t (Abs.Ident name) args body) = do
    t' <- pass1Type t
    args_ <- mapM pass1Arg args
    let args' = case maybeClass of
            Nothing -> args_
            Just className -> (pos, (Class className), "self") : args_
    foldM_
        (\vars (p, _, ident) ->
            if S.member ident vars
                then throwError
                    (p, "argument " ++ show ident ++ " defined multiple times")
                else return $ S.insert ident vars
        )
        S.empty
        args'
    (oldVenv, depth, _) <- get
    envModL <- mapM (\(_, type_, ident) -> do
            tmpName <- createVarName
            return (ident, (type_, depth, tmpName))) args'
    let envModification = M.fromList envModL
    let newVenv = M.union envModification oldVenv
    (_, _, seed) <- get
    put (newVenv, depth + 1, seed)
    let args'' = map (\(p, type_, ident) -> let (_, _, tmpName) = Maybe.fromJust (M.lookup ident envModification) in (p, type_, tmpName)) args'
    body' <- local
        (\(fenv, cenv, _, c) -> (fenv, cenv, t', c)) (pass1Block body)
    (_, _, seed') <- get
    put (oldVenv, depth, seed')
    if checkReturnBlock body' /= RSUnknown || t' == Void
        then return $ FunDef pos t' ("_lat_" ++ name) args'' body'
        else throwError
            (pos, "function returning non-void doesn't have a return")

pass1Arg :: Abs.Arg Position -> Pass1M Arg
pass1Arg (Abs.Arg pos t (Abs.Ident ident)) = do
    t' <- pass1Type t
    return (pos, t', ident)

pass1Block :: Abs.Block Position -> Pass1M Block
pass1Block (Abs.Block pos stmts) = do
    (oldVenv, depth, seed) <- get
    put (oldVenv, depth + 1, seed)
    stmts' <- mapM pass1Stmt stmts
    (_, _, seed') <- get
    put (oldVenv, depth, seed')
    return $ Block pos stmts'

-- can assign value of type t1 to lvalue of type t2
isAssignable :: Type -> Type -> Pass1M Bool
isAssignable t1 t2 = do
    if t1 == t2
        then return True
        else case t1 of
            Class className -> do
                (_, cenv, _, _) <- ask
                case M.lookup className cenv of
                    Nothing -> undefined
                    Just (_, _, parent) ->
                        case parent of
                            Nothing -> return False
                            Just parentName ->
                                isAssignable (Class parentName) t2
            _ -> return False

pass1Stmt :: Abs.Stmt Position -> Pass1M Stmt
pass1Stmt (Abs.Empty pos) = return $ Empty pos
pass1Stmt (Abs.BStmt pos block) = BStmt pos <$> pass1Block block
pass1Stmt (Abs.Decl pos t items) = do
    t' <- pass1Type t
    items' <- mapM (pass1Item t') items
    return $ Decl pos t' items'
pass1Stmt (Abs.Ass pos e1 e2) = do
    lval <- pass1Expr e1 >>= getLvalue
    expr <- pass1Expr e2
    allowAssign <- isAssignable (typeOfExpr expr) (typeOfLvalue lval)
    if allowAssign
        then return $ Ass pos lval expr
        else throwError
            (pos,
            "cannot assign expression of type " ++ show (typeOfExpr expr) ++
            " to variable of type " ++ show (typeOfLvalue lval))
pass1Stmt (Abs.Incr pos expr) = do
    expr' <- pass1Expr expr
    lval <- getLvalue expr'
    return (Ass pos lval (EIntOp Int pos expr' Add (ELitInt pos 1)))
pass1Stmt (Abs.Decr pos expr) = do
    expr' <- pass1Expr expr
    lval <- getLvalue expr'
    return (Ass pos lval (EIntOp Int pos expr' Sub (ELitInt pos 1)))
pass1Stmt (Abs.Ret pos expr) = do
    expr' <- pass1Expr expr
    (_, _, retType, _) <- ask
    if typeOfExpr expr' /= retType
        then throwError
            (pos,
            "cannot return something of type " ++ show (typeOfExpr expr') ++
            " from a function returning " ++ show retType)
        else return $ Ret pos (Just expr')
pass1Stmt (Abs.VRet pos) = do
    (_, _, retType, _) <- ask
    if retType /= Void
        then throwError
            (pos,
            "cannot have empty return in function returning " ++ show retType)
        else return $ Ret pos Nothing
pass1Stmt (Abs.Cond pos cond body) = do
    cond' <- pass1Expr cond
    (oldVenv, depth, seed) <- get
    put (oldVenv, depth + 1, seed)
    body' <- pass1Stmt body
    (_, _, seed') <- get
    put (oldVenv, depth, seed')
    case typeOfExpr cond' of
        Bool ->
            case cond' of
                ELitBool _ True -> return body'
                ELitBool _ False -> return $ Empty pos
                _ -> return $ Cond pos cond' body' Nothing
        _ -> throwError (pos, "condition in if statement must be boolean")
pass1Stmt (Abs.CondElse pos cond bodyIf bodyElse) = do
    cond' <- pass1Expr cond
    (oldVenv, depth, seed) <- get
    put (oldVenv, depth + 1, seed)
    bodyIf' <- pass1Stmt bodyIf
    (_, _, seed') <- get
    put (oldVenv, depth + 1, seed')
    bodyElse' <- pass1Stmt bodyElse
    (_, _, seed'') <- get
    put (oldVenv, depth, seed'')
    case typeOfExpr cond' of
        Bool ->
            case cond' of
                ELitBool _ True -> return bodyIf'
                ELitBool _ False -> return bodyElse'
                _ -> return $ Cond pos cond' bodyIf' (Just bodyElse')
        _ -> throwError (pos, "condition in if statement must be boolean")
pass1Stmt (Abs.While pos cond body) = do
    cond' <- pass1Expr cond
    (oldVenv, depth, seed) <- get
    put (oldVenv, depth + 1, seed)
    body' <- pass1Stmt body
    (_, _, seed') <- get
    put (oldVenv, depth, seed')
    case typeOfExpr cond' of
        Bool ->
            case cond' of
                ELitBool _ False -> return $ Empty pos
                _ -> return $ While pos cond' body'
        _ -> throwError (pos, "condition in while statement must be boolean")
pass1Stmt (Abs.SExp pos expr) = SExp pos <$> pass1Expr expr
pass1Stmt (Abs.For pos t (Abs.Ident ident) iterable body) =
    let
        notIterable = throwError
            (pos, "type of variable to iterate over is not an array")
    in do
    t' <- pass1Type t
    iter' <- pass1Expr iterable
    case typeOfExpr iter' of
        Array iterType -> if t' == iterType
            then do
                (oldVenv, depth, seed) <- get
                iterItem@(Item _ iterName _) <-
                    pass1Item iterType (Abs.NoInit pos (Abs.Ident ident))
                countName <- createVarName
                put
                    (M.insert ident (iterType, depth, iterName) oldVenv,
                        depth + 1,
                        seed)
                body' <- pass1Stmt body
                (_, _, seed') <- get
                put (oldVenv, depth, seed')
                let countDecl =
                        Decl pos Int [Item pos countName (ELitInt pos 0)]
                let iterDecl = Decl pos iterType [iterItem]
                let whileCond =
                        ERel
                            pos
                            (EVar Int pos countName)
                            Lth
                            (EClassField Int pos iter' "length")
                let assignIter =
                        Ass
                            pos
                            (VarRef iterType pos iterName)
                            (EArrAt iterType pos iter' (EVar Int pos countName))
                let incrCount =
                        Ass
                            pos
                            (VarRef Int pos countName)
                            (EIntOp
                                Int
                                pos
                                (EVar Int pos countName)
                                Add
                                (ELitInt pos 1))
                let whileBody =
                        BStmt pos $ Block pos [assignIter, body', incrCount]
                let whileStmt = While pos whileCond whileBody
                return $ BStmt pos $ Block pos [countDecl, iterDecl, whileStmt]
            else throwError
                (pos,
                "type mismatch in for: can't iterate over array of " ++
                show iterType ++ " with variable of type " ++ show t')
        Int -> notIterable
        Bool -> notIterable
        String_ -> notIterable
        Void -> notIterable
        Class _ -> notIterable


-- throw an error if we can't declare a particular variable
checkdecl :: Position -> Ident -> Type -> Pass1M Ident
checkdecl pos ident t = do
    varName <- createVarName
    (venv, depth, seed) <- get
    case M.lookup ident venv of
        Nothing -> do
            put (M.insert ident (t, depth, varName) venv, depth, seed)
            return varName
        Just (_, depth', _) -> if depth' < depth
            then do
                put (M.insert ident (t, depth, varName) venv, depth, seed)
                return varName
            else throwError (pos, ident ++ " has already been declared")
pass1Item :: Type -> Abs.Item Position -> Pass1M Item
pass1Item t (Abs.NoInit pos (Abs.Ident ident)) = do
    varName <- checkdecl pos ident t
    case t of
        Int -> return $ Item pos varName (ELitInt pos 0)
        Bool -> return $ Item pos varName (ELitBool pos False)
        String_ -> return $ Item pos varName (EString pos "")
        Void -> throwError  (pos, "cannot declare variables of type void")
        Class _ -> return $ Item pos varName (ECoerce pos t)
        Array _ -> return $ Item pos varName (ECoerce pos t)
pass1Item t (Abs.Init pos (Abs.Ident ident) expr) = do
    expr' <- pass1Expr expr
    canAssign <- isAssignable (typeOfExpr expr') t
    if not canAssign
        then throwError
            (pos, "cannot assign value of type " ++ show (typeOfExpr expr') ++
             " to variable of type " ++ show t)
        else do
            varName <- checkdecl pos ident t
            return $ Item pos varName expr'

notLvalue :: Position -> String -> Pass1M a
notLvalue p s = throwError (p, s ++ " cannot be used as lvalue")

getLvalue :: Expr -> Pass1M Lvalue
getLvalue (ENewArr _ pos _ _) = notLvalue pos "array declaration"
getLvalue (ENewObj pos _ ) = notLvalue pos "object declaration"
getLvalue (EVar t pos ident) = return $ VarRef t pos ident
getLvalue (ELitInt pos _) = notLvalue pos "integer literal"
getLvalue (ELitBool pos _) = notLvalue pos "boolean literal"
getLvalue (EString pos _) = notLvalue pos "string literal"
getLvalue (ECoerce pos _) = notLvalue pos "coercion expression"
getLvalue (EApp _ pos _ _) = notLvalue pos "function application"
getLvalue (EClassMethod _ pos _ _ _) = notLvalue pos "method aplication"
getLvalue (EClassField t pos expr ident) = do
    class_ <- getLvalue expr
    -- we don't have to check here whether such attribute exists, because
    -- creating Expr did that check already
    case typeOfLvalue class_ of
        Class _ -> return $ ClassAttr t pos class_ ident
        Array _ -> throwError (pos, "cannot use array length as lvalue")
        _ -> undefined
getLvalue (EArrAt t pos e1 e2) = do
    arr <- getLvalue e1
    return $ ArrRef t pos arr e2
getLvalue (Neg pos _) = notLvalue pos "integer negation"
getLvalue (Not pos _) = notLvalue pos "logical negation"
getLvalue (EIntOp _ pos _ _ _) = notLvalue pos "binary operation"
getLvalue (ERel pos _ _ _) = notLvalue pos "relation on integers"
getLvalue (EBoolOp pos _ _ _) = notLvalue pos "operation on booleans"

typeOfLvalue :: Lvalue -> Type
typeOfLvalue (VarRef t _ _) = t
typeOfLvalue (ClassAttr t _ _ _) = t
typeOfLvalue (ArrRef t _ _ _) = t

undeclaredIdentifier :: Position -> Ident -> Pass1M a
undeclaredIdentifier pos ident =
    throwError (pos, "undeclared identifier " ++ ident)

undeclaredFunction :: Position -> Ident -> Pass1M a
undeclaredFunction pos ident = throwError (pos, "undeclared function " ++ ident)

undeclaredField :: Position -> Ident -> Ident -> Pass1M a
undeclaredField pos fieldIdent classIdent =
    throwError (pos, "class " ++ classIdent ++ " has no field " ++ fieldIdent)

ressolveField :: Position -> Ident -> Ident -> Ident -> Pass1M Type
ressolveField pos fieldIdent classIdent origClassIdent = do
    (_, cenv, _, _) <- ask
    case M.lookup classIdent cenv of
        Nothing -> undefined
        Just (fields, _, parent) -> case M.lookup fieldIdent fields of
            Just t -> return t
            Nothing -> case parent of
                Nothing -> undeclaredField pos fieldIdent origClassIdent
                Just parentIdent ->
                        ressolveField pos fieldIdent parentIdent origClassIdent

ressolveVariable :: Position -> Ident -> Ident -> Pass1M Expr
ressolveVariable pos varIdent classIdent = do
    (_, cenv, _, _) <- ask
    case M.lookup classIdent cenv of
        Nothing -> undefined
        Just (fields, _, parent) -> case M.lookup varIdent fields of
            Just t -> do
                (venv, _, _) <- get
                let (selfType, _, selfName) = Maybe.fromJust $ M.lookup "self"  venv
                return $ EClassField
                        t
                        pos
                        (EVar selfType pos selfName)
                        varIdent
            Nothing -> case parent of
                Nothing -> undeclaredIdentifier pos varIdent
                Just parentIdent -> ressolveVariable pos varIdent parentIdent

ressolveFunction :: Position -> Ident -> Ident -> Pass1M (Type, [Type], Ident)
ressolveFunction pos funIdent classIdent = do
    (_, cenv, _, _) <- ask
    case M.lookup classIdent cenv of
        Nothing -> undefined
        Just (_, methods, parent) -> case M.lookup funIdent methods of
            Just t -> return t
            Nothing -> case parent of
                Nothing -> undeclaredFunction pos funIdent
                Just parentIdent -> ressolveFunction pos funIdent parentIdent

checkFArgs :: Position -> Ident -> [Type] -> [Type] -> Pass1M ()
checkFArgs pos funIdent actualTypes expectedTypes = do
    when
        (length expectedTypes /= length actualTypes)
        (throwError
            (pos,
            "incorrect number of arguments in function call: expected " ++
            show (length expectedTypes) ++ " got " ++
            show (length actualTypes)))
    canAssign <- foldM
        (\acc (t1, t2) -> if acc then isAssignable t1 t2 else return acc)
        True
        (zip actualTypes expectedTypes)
    when (not canAssign)
        (throwError
            (pos,
            "incorrect types of arguments in call to function " ++
            funIdent ++ ", expected " ++ show expectedTypes ++ ", got " ++
            show actualTypes))

pass1Expr :: Abs.Expr Position -> Pass1M Expr
pass1Expr (Abs.ENewArr pos t e) = do
    t' <- pass1Type t
    e' <- pass1Expr e
    case typeOfExpr e' of
        Int -> return $ ENewArr (Array t') pos t' e'
        _ -> throwError (pos, "array size has to be an integer")
pass1Expr (Abs.ENewObj pos t) = do
    t' <- pass1Type t
    case t' of
        Class _ -> return $ ENewObj pos t'
        _ -> throwError (pos,
                "cannot declare values of type " ++ show t' ++ " with new")
pass1Expr (Abs.EVar pos (Abs.Ident ident)) = do
    (venv, _, _) <- get
    case M.lookup ident venv of
        Just (t, _, tmpName) -> return $ EVar t pos tmpName
        Nothing -> do
            (_, _, _, className) <- ask
            case className of
                Nothing -> undeclaredIdentifier pos ident
                Just classIdent -> ressolveVariable pos ident classIdent
pass1Expr (Abs.ELitInt pos n) = return $ ELitInt pos n
pass1Expr (Abs.ELitTrue pos) = return $ ELitBool pos True
pass1Expr (Abs.ELitFalse pos) = return $ ELitBool pos False
pass1Expr (Abs.EString pos s) = return $ EString pos s
pass1Expr (Abs.EClassCoerce pos name) =
    case name of
        Abs.EVar _ (Abs.Ident className) -> do
            (_, cenv, _, _) <- ask
            case M.lookup className cenv of
                Nothing -> throwError (pos, "unknown type: " ++ className)
                Just _ -> return $ ECoerce pos (Class className)
        _ -> throwError (pos, "expression cannot be used as a type")
pass1Expr (Abs.EClassArrCoerce pos t) = do
    t' <- pass1ArrayType t
    return $ ECoerce pos t'
pass1Expr (Abs.EApp pos (Abs.Ident funIdent) args) = do
    (fenv, _, _, _) <- ask
    ((retType, argTypes, tmpName), maybeSelf) <- case M.lookup funIdent fenv of
        Nothing ->  do
            (_, _, _, className) <- ask
            case className of
                Nothing -> undeclaredFunction pos funIdent
                Just classIdent -> do
                        t <- ressolveFunction pos funIdent classIdent
                        return (t, Just (EVar (Class classIdent) pos "self"))
        Just t -> return (t, Nothing)
    args' <- mapM pass1Expr args
    let argTypes' = map typeOfExpr args'
    checkFArgs pos funIdent argTypes' argTypes
    case maybeSelf of
        Just self -> return $ EClassMethod retType pos self tmpName args'
        Nothing -> return $ EApp retType pos tmpName args'
pass1Expr (Abs.EClassMethod pos classExpr (Abs.Ident methodIdent) args) = do
    classExpr' <- pass1Expr classExpr
    case typeOfExpr classExpr' of
        Class classIdent -> do
            (_, cenv, _, _) <- ask
            case M.lookup classIdent cenv of
                Nothing ->
                    throwError
                        (pos,
                            classIdent ++ " is not a correct class identifier")
                Just _ -> do
                    (retType, argTypes, tmpName) <- ressolveFunction
                        pos methodIdent classIdent
                    args' <- mapM pass1Expr args
                    let argTypes' = map typeOfExpr args'
                    checkFArgs
                        pos
                        (classIdent ++ "." ++ methodIdent)
                        argTypes'
                        argTypes
                    return $
                        EClassMethod retType pos classExpr' tmpName args'
        _ -> throwError (pos, "calling method on non-class type is forbidden")
pass1Expr (Abs.EClassField pos classExpr (Abs.Ident fieldIdent)) = do
    classExpr' <- pass1Expr classExpr
    case typeOfExpr classExpr' of
        Class classIdent -> do
            t <- ressolveField pos fieldIdent classIdent classIdent
            return $ EClassField t pos classExpr' fieldIdent
        Array _ -> if fieldIdent /= "length"
            then throwError
                (pos, "array has no member " ++ fieldIdent ++ ", only length")
            else return $ EClassField Int pos classExpr' fieldIdent
        _ -> throwError
            (pos,
            "accessing members on non-class type " ++
            show (typeOfExpr classExpr') ++ " is forbidden")
pass1Expr (Abs.EArrAt pos arrExpr indexExp) = do
    arrExp' <- pass1Expr arrExpr
    indexExp' <- pass1Expr indexExp
    case typeOfExpr indexExp' of
        Int ->
            case typeOfExpr arrExp' of
                Array t -> return $ EArrAt t pos arrExp' indexExp'
                _ -> throwError (pos, "cannot index non-array type")
        _ -> throwError (pos, "array index must be an integer")
pass1Expr (Abs.Neg pos expr) = do
    expr' <- pass1Expr expr
    case typeOfExpr expr' of
        Int -> return $ optimizeConstExpr $ Neg pos expr'
        _ -> throwError
            (pos,
            "type mismatch - cannot perform integer negation on non-integer expressions")
pass1Expr (Abs.Not pos expr) = do
    expr' <- pass1Expr expr
    case typeOfExpr expr' of
        Bool -> return $ Not pos expr'
        _ -> do
            throwError
                (pos,
                "type mismatch - cannot perform boolean negation on non-boolean expressions")
pass1Expr (Abs.EMul pos e1 mulop e2) =
    let
        getPosMul :: Abs.MulOp Position -> Position
        getPosMul (Abs.Times p) = p
        getPosMul (Abs.Div p) = p
        getPosMul (Abs.Mod p) = p
        checkIf0 :: Expr -> String -> Pass1M ()
        checkIf0 (ELitInt _ 0) name = throwError (pos, name ++ " by zero")
        checkIf0 _ _ = return ()
    in do
    e1' <- pass1Expr e1
    e2' <- pass1Expr e2
    case (typeOfExpr e1', typeOfExpr e2') of
        (Int, Int) -> do
            let createEMul f op = do {
                case (e1', e2') of
                    (ELitInt _ n, ELitInt _ m) -> return $ ELitInt pos (f n m)
                    _ -> return $ EIntOp Int pos e1' op e2'
            }
            case mulop of
                Abs.Times _ -> optimizeConstExpr <$> createEMul (*) Mul
                Abs.Div _ -> checkIf0 e2' "division" *> createEMul div Div
                Abs.Mod _ -> checkIf0 e2' "modulo" *> createEMul mod Mod
        _ -> throwError
            (getPosMul mulop,
             "type mismatch - both operands should be integers")
pass1Expr (Abs.EAdd pos e1 addop e2) =
    let
        getPosAdd :: Abs.AddOp Position -> Position
        getPosAdd (Abs.Plus p) = p
        getPosAdd (Abs.Minus p) = p
    in do
    e1' <- pass1Expr e1
    e2' <- pass1Expr e2
    case (typeOfExpr e1', typeOfExpr e2') of
        (Int, Int) -> do
            let createEAdd f op = do {
                case (e1', e2', op) of
                    (ELitInt _ n, ELitInt _ m, _) ->
                        return $ ELitInt pos (f n m)
                    _ -> return $ EIntOp Int pos e1' op e2'
            }
            case addop of
                Abs.Plus _ -> optimizeConstExpr <$> createEAdd (+) Add
                Abs.Minus _ -> createEAdd (-) Sub
        (String_, String_) ->
            case addop of
                Abs.Minus _ ->
                    throwError
                        (getPosAdd addop,
                        "type mismatch - both operands should be integers")
                Abs.Plus _ -> return $ EApp String_ pos "_stradd" [e1', e2']
        _ -> throwError
            (getPosAdd addop,
            "type mismatch - both operands should be integers")
pass1Expr (Abs.ERel pos e1 relop e2) =
    let
        getPosRel :: Abs.RelOp Position -> Position
        getPosRel (Abs.LTH p) = p
        getPosRel (Abs.LE p) = p
        getPosRel (Abs.GTH p) = p
        getPosRel (Abs.GE p) = p
        getPosRel (Abs.EQU p) = p
        getPosRel (Abs.NE p) = p
    in do
    e1' <- pass1Expr e1
    let typee1 = typeOfExpr e1'
    e2' <- pass1Expr e2
    let typee2 = typeOfExpr e2'
    let createERelInt f op = do {
        case (e1', e2') of
            (ELitInt _ n, ELitInt _ m) -> return $ ELitBool pos (f n m)
            _ -> return $ ERel pos e1' op e2'
    }
    let createERelString f fname = do {
        case (e1', e2') of
            (EString _ n, EString _ m) -> return $ ELitBool pos (f n m)
            _ -> return $ EApp String_ pos fname [e1', e2']
    }
    let createERelBool f op = do {
        case (e1', e2') of
            (ELitBool _ n, ELitBool _ m) -> return $ ELitBool pos (f n m)
            _ -> return $ ERel pos e1' op e2'
    }
    let createERelOther op = return $ ERel pos e1' op e2'
    let mismatchIntegers =
            throwError
                (getPosRel relop,
                "type mismatch - both operands should be integers")
    let mismatchSameType =
            throwError
                (getPosRel relop,
                "type mismatch - both operands should be of the same type")
    case relop of
        Abs.LTH _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (<) Lth
                _ -> mismatchIntegers
        Abs.LE _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (<=) Le
                _ -> mismatchIntegers
        Abs.GTH _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (>) Gth
                _ -> mismatchIntegers
        Abs.GE _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (>=) Ge
                _ -> mismatchIntegers
        Abs.EQU _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (==) Equ
                (String_, String_) -> createERelString (==) "_strcmp"
                (Bool, Bool) -> createERelBool (==) Equ
                (Array t1, Array t2) -> if t1 == t2
                    then createERelOther Equ
                    else mismatchSameType
                (Class name1, Class name2) -> if name1 == name2
                    then createERelOther Equ
                    else mismatchSameType
                _ -> mismatchSameType
        Abs.NE _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (/=) Neq
                (String_, String_) -> createERelString (/=) "_strncmp"
                (Bool, Bool) -> createERelBool (/=) Neq
                (Array t1, Array t2) -> if t1 == t2
                    then createERelOther Neq
                    else mismatchSameType
                (Class name1, Class name2) -> if name1 == name2
                    then createERelOther Neq
                    else mismatchSameType
                _ -> mismatchSameType
pass1Expr (Abs.EAnd pos e1 e2) = createBoolOp pos e1 e2 (&&) And
pass1Expr (Abs.EOr pos e1 e2) = createBoolOp pos e1 e2 (||) Or

createBoolOp :: Position -> Abs.Expr Position -> Abs.Expr Position -> (Bool -> Bool -> Bool) -> BoolOp -> Pass1M Expr
createBoolOp pos e1 e2 f op = do
    e1' <- pass1Expr e1
    e2' <- pass1Expr e2
    let createEBool = do {
        case (e1', e2') of
            (ELitBool _ n, ELitBool _ m) -> return $ ELitBool pos (f n m)
            _ -> return $ optimizeConstExpr $ EBoolOp pos e1' op e2'
    }
    case (typeOfExpr e1', typeOfExpr e2') of
        (Bool, Bool) -> createEBool
        _ ->
            throwError (pos, "type mismatch - both operands should be booleans")

optimizeConstExpr :: Expr -> Expr
optimizeConstExpr (EIntOp Int p (EIntOp _ _ (ELitInt p' n) Add expr) Add (ELitInt _ m)) =
    EIntOp Int p (ELitInt p' (n + m)) Add expr
optimizeConstExpr (EIntOp Int p (EIntOp _ _ expr Add (ELitInt p' n)) Add (ELitInt _ m)) =
    EIntOp Int p (ELitInt p' (n + m)) Add expr
optimizeConstExpr (EIntOp Int p (ELitInt p' m) Add (EIntOp _ _ (ELitInt _ n) Add expr)) =
    EIntOp Int p (ELitInt p' (n + m)) Add expr
optimizeConstExpr (EIntOp Int p (ELitInt p' m) Add (EIntOp _ _ expr Add (ELitInt _ n))) =
    EIntOp Int p (ELitInt p' (n + m)) Add expr
optimizeConstExpr (EIntOp Int p (EIntOp _ _ (ELitInt p' n) Mul expr) Mul (ELitInt _ m)) =
    EIntOp Int p (ELitInt p' (n * m)) Mul expr
optimizeConstExpr (EIntOp Int p (EIntOp _ _ expr Mul (ELitInt p' n)) Mul (ELitInt _ m)) =
    EIntOp Int p (ELitInt p' (n * m)) Mul expr
optimizeConstExpr (EIntOp Int p (ELitInt p' m) Mul (EIntOp _ _ (ELitInt _ n) Mul expr)) =
    EIntOp Int p (ELitInt p' (n * m)) Mul expr
optimizeConstExpr (EIntOp Int p (ELitInt p' m) Mul (EIntOp _ _ expr Mul (ELitInt _ n))) =
    EIntOp Int p (ELitInt p' (n * m)) Mul expr
optimizeConstExpr (EBoolOp _ (ELitBool _ True) And expr) = expr
optimizeConstExpr (EBoolOp _ expr And (ELitBool _ True)) = expr
optimizeConstExpr (EBoolOp p (ELitBool _ True) Or _) = ELitBool p True
optimizeConstExpr (EBoolOp _ (ELitBool _ False) Or expr) = expr
optimizeConstExpr (EBoolOp _ expr Or (ELitBool _ False)) = expr
optimizeConstExpr (EBoolOp p (ELitBool _ False) And _) = ELitBool p False
optimizeConstExpr (Neg p (ELitInt _ n)) = ELitInt p (-n)
optimizeConstExpr expr = expr

typeOfExpr :: Expr -> Type
typeOfExpr (ENewArr t _ _ _) = t
typeOfExpr (ENewObj _ t) = t
typeOfExpr (EVar t _ _) = t
typeOfExpr (ELitInt _ _) = Int
typeOfExpr (ELitBool _ _) = Bool
typeOfExpr (EString _ _) = String_
typeOfExpr (ECoerce _ t) = t
typeOfExpr (EApp t _ _ _) = t
typeOfExpr (EClassMethod t _ _ _ _) = t
typeOfExpr (EClassField t _ _ _) = t
typeOfExpr (EArrAt t _ _ _) = t
typeOfExpr (Neg _ _ ) = Int
typeOfExpr (Not _ _) = Bool
typeOfExpr (EIntOp t _ _ _ _) = t
typeOfExpr ERel{} = Bool
typeOfExpr EBoolOp{} = Bool

getTypesFromClassBody :: (M.Map Ident Type, M.Map Ident (Type, [Type], Ident)) -> Abs.ClassBody Position -> Pass1M (M.Map Ident Type, M.Map Ident (Type, [Type], Ident))
getTypesFromClassBody (fields, methods) (Abs.AttrFun _ (Abs.FunDef _ t (Abs.Ident ident) args _)) = do
    t' <- pass1Type t
    args' <- mapM pass1Arg args
    let argTypes = map (\(_, type_, _) -> type_) args'
    return (fields, M.insert ident (t', argTypes, "_lat_" ++ ident) methods)
getTypesFromClassBody (fields, methods) (Abs.Attr _ t (Abs.Ident ident)) = do
    t' <- pass1Type t
    return (M.insert ident t' fields, methods)

createClassEnv :: [(Position, Ident, [Abs.ClassBody Position])] -> [(Position, Ident, Ident, [Abs.ClassBody Position])] -> Pass1M Cenv
createClassEnv classes classesExt = do
    let classList =
            map (\(_, name, _) ->  name) classes ++
            map (\(_, name, _, _) -> name) classesExt
    let classNames = S.fromList classList
    foldM (\() (p, _, parentName, _) ->
        when
            (not (S.member parentName classNames))
            (throwError (p, "undeclared class " ++ parentName)))
        () classesExt
    let graph =
            map (\(pos, name, parentName, _) ->
                    ((pos, name), name, [parentName]))
                classesExt
    let sccs = map G.flattenSCC $ G.stronglyConnComp graph
    let tmpEnv =
            M.fromList
                (map (\name -> (name, (M.empty, M.empty, Nothing))) classList)
    foldM (\() scc ->
        when
            (length scc > 1)
            (throwError
                (fst (head scc),
                "cycle in inhertiance graph detected on the following classes: " ++
                show (map snd scc))))
        () sccs
    local (const (M.empty, tmpEnv, Void, Nothing)) (do
        baseClassEnv <- foldM
            (\env (p, className, body) -> do
                    (fields, methods) <-
                        foldM getTypesFromClassBody (M.empty, M.empty) body
                    case M.lookup className env of
                        Nothing ->
                            return $
                                M.insert
                                    className
                                    (fields, methods, Nothing)
                                    env
                        Just _ ->
                            throwError
                                (p, "class " ++ className ++ " redefined")
            )
            M.empty
            classes
        foldM (\env (p, className, parentName, body) -> do
                when
                    (className == parentName)
                    (throwError
                        (p, "class " ++ className ++ " deriving from itself"))
                (fields, methods) <-
                    foldM getTypesFromClassBody (M.empty, M.empty) body
                case M.lookup className env of
                    Nothing -> return $
                        M.insert
                            className
                            (fields, methods, Just parentName)
                            env
                    Just _ ->
                        throwError (p, "class " ++ className ++ " redefined")
            )
            baseClassEnv
            classesExt
        )

pass1Classes :: [(Position, Ident, [Abs.ClassBody Position])] -> [(Position, Ident, Ident, [Abs.ClassBody Position])] -> Pass1M [ClassDef]
pass1Classes classes classesExt =
    let
        splitBody (Abs.AttrFun _ fnDef) = Left fnDef
        splitBody (Abs.Attr pos t (Abs.Ident ident)) = Right (pos, t, ident)
    in do
    classes' <- mapM
        (\(pos, className, body) -> do
            let (fns, attrs) = partitionWith splitBody body
            (oldVenv, depth, seed) <- get
            let newVenv =
                    M.insert "self" (Class className, depth, "self") oldVenv
            put (newVenv, depth, seed)
            fields <- mapM
                (\(p, t, ident) -> do
                    t' <- pass1Type t
                    return $ Field p t' ident)
                attrs
            methods <- local
                (\(fenv, cenv, type_, _) -> (fenv, cenv, type_, Just className))
                (mapM (pass1FunDef (Just className)) fns)
            (_, _, seed') <- get
            put (oldVenv, depth, seed')
            return $ ClassDef pos className Nothing fields methods
        ) classes
    classesExt' <- mapM
        (\(pos, className, parentName, body) -> do
            let (fns, attrs) = partitionWith splitBody body
            (oldVenv, depth, seed) <- get
            let newVenv =
                    M.insert "self" (Class className, depth, "self") oldVenv
            put (newVenv, depth, seed)
            fields <- mapM
                (\(p, t, ident) -> do
                    t' <- pass1Type t
                    return $ Field p t' ident)
                attrs
            methods <- local
                (\(fenv, cenv, type_, _) ->
                    (fenv, cenv, type_, Just className))
                (mapM (\fn -> do
                    fn'@(FunDef _ retType funIdent args _) <- (pass1FunDef
                            (Just className)) fn
                    parentType <- catchError
                        (Just <$> ressolveFunction pos funIdent parentName)
                        (\_ -> return Nothing)
                    case parentType of
                        Just (retType', argTypes', _) ->
                            let argTypes = map (\(_, t, _) -> t) args in
                            if retType' == retType && argTypes' == argTypes
                                then return fn'
                                else throwError
                                    (pos,
                                    "overloaded function type has to be exactly the same as original")
                        Nothing -> return fn')
                     fns)
            (_, _, seed') <- get
            put (oldVenv, depth, seed')
            return $ ClassDef pos className (Just parentName) fields methods
        ) classesExt
    return $ classes' ++ classesExt'

-- first pass through ast, frontend
pass1 :: Abs.Program Position -> Pass1M Program
pass1 (Abs.Program p tlds) =
    let
        initialFenv = M.fromList
            [("printInt", (Void, [Int], "printInt")),
            ("printString", (Void, [String_], "printString")),
            ("error", (Void, [], "error")),
            ("readInt", (Int, [], "readInt")),
            ("readString", (String_, [], "readString"))]
    in
    let
        helper fdefs (Abs.FnDef pos (Abs.FunDef _ t (Abs.Ident ident) args _)) = do
            t' <- pass1Type t
            args' <- mapM (\(Abs.Arg _ type_ _) -> pass1Type type_) args
            case M.lookup ident fdefs of
                Nothing -> return $ M.insert ident (t', args', "_lat_" ++ ident) fdefs
                Just _ -> throwError (pos, "function " ++ ident ++ " redefined")
        helper fdefs Abs.ClassDef{} = return fdefs
        helper fdefs Abs.ClassExtDef{} = return fdefs
        helper2 (pos, fdefs, cdefs, cedefs) (Abs.FnDef _ fundef@(Abs.FunDef currentPos _ (Abs.Ident name) _ _)) =
            if name == "main"
                then (currentPos, fundef : fdefs, cdefs, cedefs)
                else (pos, fundef : fdefs, cdefs, cedefs)
        helper2 (pos, fdefs, cdefs, cedefs) (Abs.ClassDef pos' (Abs.Ident ident) cbody) = (pos, fdefs, (pos', ident, cbody) : cdefs, cedefs)
        helper2 (pos, fdefs, cdefs, cedefs) (Abs.ClassExtDef pos' (Abs.Ident name) (Abs.Ident parentName) body) = (pos, fdefs, cdefs, (pos', name, parentName, body) : cedefs)
    in do
        let (mainPos, fundefs, cdefs, cedefs) = foldl helper2 (Nothing, [], [], []) tlds
        cenv <- createClassEnv cdefs cedefs
        fenv <- local (const (M.empty, cenv, Void, Nothing)) (foldM helper initialFenv tlds)
        case M.lookup "main" fenv of
            Nothing -> throwError (p, "no main function specified")
            Just (retType, argTypes, _) ->
                when (retType /= Int || argTypes /= [])
                    (throwError (mainPos, "Incorrect type of main function: its signature should be `int main()`"))
--        when (not (null cdefs) || not (null cedefs))
--            (throwError (Nothing, "Detected classes declarations in the program, those are not supported yet"))
        fundefs' <-
            local
                (const (fenv, cenv, Void, Nothing))
                (mapM (pass1FunDef Nothing) fundefs)
        classdefs <-
            local
                 (const (fenv, cenv, Void, Nothing))
                 (pass1Classes cdefs cedefs)
        return $ Program p classdefs fundefs'

