{-# Options -Wall -Wname-shadowing #-}

module Frontend where

import qualified Data.Map as M
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Debug.Trace

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

data Program = Program Position [ClassDef] [FunDef]
data ClassDef = ClassDef Position Ident (Maybe Ident) [ClassBody]
data ClassBody = AttrVar Position Type Ident | AttrFun Position FunDef
data FunDef = FunDef Position Type Ident [Arg] Block
type Arg = (Position, Type, Ident)
data Block = Block Position [Stmt]
data Stmt
    = Empty Position
    | BStmt Position Block
    | Decl Position Type [Item]
    | Ass Position Lvalue Expr
    | Incr Position Lvalue
    | Decr Position Lvalue
    | Ret Position (Maybe Expr)
    | Cond Position Expr Stmt (Maybe Stmt)
    | While Position Expr Stmt
    | SExp Position Expr
    | For Position Ident Expr Stmt
data Item = Item Position Ident (Maybe Expr)
data Expr
    = ENewArr Position Type Expr
    | ENewObj Position Type
    | EVar Position Ident
    | ELitInt Position Integer
    | ELitBool Position Bool
    | EString Position String
    | ECoerce Position Type Expr
    | EApp Position Ident [Expr]
    | EClassMethod Position Expr Ident [Expr]
    | EClassField Position Expr Ident
    | EArrAt Position Expr Expr
    | Neg Position Expr
    | Not Position Expr
    | EIntOp Position Expr IntOp Expr
    | ERel Position Expr IntRel Expr
    | EBoolOp Position Expr BoolOp Expr
data Lvalue
    = VarRef Position Ident
    | ClassAttr Position Lvalue Ident
    | ArrRef Position Lvalue Expr

data IntOp = Mul | Div | Add | Sub | Mod
data IntRel = Lth | Le | Gth | Ge | Equ | Neq
data BoolOp = Or | And

type Depth = Integer
type Venv = M.Map Ident (Type, Depth) -- variable env
type Fenv = M.Map Ident (Type, [Type]) -- function env
type Cenv = M.Map Ident (M.Map Ident Type, M.Map Ident (Type, [Type])) -- classes env
type Pass1M = ReaderT (Fenv, Cenv) (StateT (Venv, Depth) (Except (Position, String)))

pass1BuiltinType :: (Abs.BuiltinType Position) -> Type
pass1BuiltinType (Abs.Int _) = Int
pass1BuiltinType (Abs.Str _) = String_
pass1BuiltinType (Abs.Bool _) = Bool
pass1BuiltinType (Abs.Void _) = Void

pass1ClassType :: String -> Position -> Pass1M Type
pass1ClassType ident pos = do
    (_, cenv) <- ask
    if M.member ident cenv
        then return (Array (Class ident))
        else throwError (pos, "Undeclared type: " ++ ident)

pass1ArrayType :: (Abs.ArrayType Position) -> Pass1M Type
pass1ArrayType (Abs.BuiltinArr _ type_) = return $ Array (pass1BuiltinType type_)
pass1ArrayType (Abs.UserArr pos (Abs.Ident ident)) = pass1ClassType ident pos

pass1Type :: (Abs.Type Position) -> Pass1M Type
pass1Type (Abs.BltinType _ t) = return (pass1BuiltinType t)
pass1Type (Abs.ArrType _ t) = pass1ArrayType t
pass1Type (Abs.UserType pos (Abs.Ident ident)) = pass1ClassType ident pos

pass1FunDef :: (Abs.FunDef Position) -> Pass1M FunDef
pass1FunDef (Abs.FunDef pos t (Abs.Ident name) args body) = do
    t' <- pass1Type t
    args' <- mapM pass1Arg args
    (oldVenv, depth) <- get
    let envModification = M.fromList (map (\(_, type_, ident) -> (ident, (type_, depth))) args')
    let newVenv = M.union envModification oldVenv
    put (newVenv, depth + 1)
    body' <- pass1Block body
    put (oldVenv, depth)
    return $ FunDef pos t' name args' body'

pass1Arg :: (Abs.Arg Position) -> Pass1M Arg
pass1Arg (Abs.Arg pos t (Abs.Ident ident)) = do
    t' <- pass1Type t
    return (pos, t', ident)

pass1Block :: (Abs.Block Position) -> Pass1M Block
pass1Block (Abs.Block pos stmts) = do
    (oldVenv, depth) <- get
    put (oldVenv, depth + 1)
    stmts' <- mapM pass1Stmt stmts
    put (oldVenv, depth)
    return $ Block pos stmts'

pass1Stmt :: (Abs.Stmt Position) -> Pass1M Stmt
pass1Stmt (Abs.Empty pos) = return $ Empty pos
pass1Stmt (Abs.BStmt pos block) = BStmt pos <$> pass1Block block
pass1Stmt (Abs.Decl pos t items) = do
    t' <- pass1Type t
    items' <- mapM (pass1Item t') items
    return $ Decl pos t' items'
pass1Stmt (Abs.Ass pos e1 e2) = do
    lval <- pass1Expr e1 >>= getLvalue
    expr <- pass1Expr e2
    lvalT <- typeOfLvalue lval
    exprT <- typeOfExpr expr
    if lvalT == exprT
        then return $ Ass pos lval expr
        else throwError (pos, "cannot assign expression of type " ++ show exprT ++ " to variable of type " ++ show lvalT)
pass1Stmt (Abs.Incr pos expr) = Incr pos <$> (pass1Expr expr >>= getLvalue)
pass1Stmt (Abs.Decr pos expr) = Decr pos <$> (pass1Expr expr >>= getLvalue)
pass1Stmt (Abs.Ret pos expr) = Ret pos <$> (Just <$> pass1Expr expr)
pass1Stmt (Abs.VRet pos) = return $ Ret pos Nothing
pass1Stmt (Abs.Cond pos cond body) = do
    cond' <- pass1Expr cond
    body' <- pass1Stmt body
    type_ <- typeOfExpr cond'
    case type_ of
        Bool -> do
            case cond' of
                ELitBool _ True -> return body'
                ELitBool _ False -> return $ Empty pos
                _ -> return $ Cond pos cond' body' Nothing
        _ -> throwError (pos, "condition in if statement must be boolean")
pass1Stmt (Abs.CondElse pos cond bodyIf bodyElse) = do
    cond' <- pass1Expr cond
    bodyIf' <- pass1Stmt bodyIf
    bodyElse' <- pass1Stmt bodyElse
    type_ <- typeOfExpr cond'
    case type_ of
        Bool -> do
            case cond' of
                ELitBool _ True -> return bodyIf'
                ELitBool _ False -> return bodyElse'
                _ -> return $ Cond pos cond' bodyIf' (Just bodyElse')
        _ -> throwError (pos, "condition in if statement must be boolean")
pass1Stmt (Abs.While pos cond body) = do
    cond' <- pass1Expr cond
    body' <- pass1Stmt body
    type_ <- typeOfExpr cond'
    case type_ of
        Bool -> do
            case cond' of
                ELitBool _ False -> return $ Empty pos
                _ -> return $ While pos cond' body'
        _ -> throwError (pos, "condition in while statement must be boolean")
pass1Stmt (Abs.SExp pos expr) = SExp pos <$> pass1Expr expr
pass1Stmt (Abs.For pos t (Abs.Ident ident) iterable body) =
    let
        notIterable = throwError (pos, "type of variable to iterate over is not an array")
    in do
    t' <- pass1Type t
    iter' <- pass1Expr iterable
    body' <- pass1Stmt body
    type_ <- typeOfExpr iter'
    case type_ of
        Array iterType -> if t' == iterType
            then return (For pos ident iter' body')
            else throwError (pos, "type mismatch in for: can't iterate over array of " ++ show iterType ++ " with variable of type " ++ show t')
        Int -> notIterable
        Bool -> notIterable
        String_ -> notIterable
        Void -> notIterable
        Class _ -> notIterable


-- throw an error if we can't declare a particular variable
checkdecl :: Position -> Ident -> Type -> Pass1M ()
checkdecl pos ident t = do
    (venv, depth)  <- get
    case M.lookup ident venv of
        Nothing -> put (M.insert ident (t, depth) venv, depth)
        Just (_, depth') -> if depth' < depth
            then put (M.insert ident (t, depth) venv, depth)
        else throwError (pos, ident ++ " has already been declared")
pass1Item :: Type -> (Abs.Item Position) -> Pass1M Item
pass1Item t (Abs.NoInit pos (Abs.Ident ident)) = do
    checkdecl pos ident t
    return $ Item pos ident Nothing
pass1Item t (Abs.Init pos (Abs.Ident ident) expr) = do
    expr' <- pass1Expr expr
    type_ <- typeOfExpr expr'
    if t /= type_
        then throwError (pos, "Cannot assign value of type " ++ show type_ ++ " to variable of type " ++ show t)
        else do
            checkdecl pos ident t
            return $ Item pos ident $ Just expr'

notLvalue :: Position -> String -> Pass1M a
notLvalue p s = throwError (p, s ++ " cannot be used as lvalue")

noAttribute :: Position -> String -> Pass1M a
noAttribute p s = throwError (p, "type " ++ s ++ " doesn't have attributes")

getLvalue :: Expr -> Pass1M Lvalue
getLvalue (ENewArr pos _ _) = notLvalue pos "array declaration"
getLvalue (ENewObj pos _ ) = notLvalue pos "object declaration"
getLvalue (EVar pos ident) = return $ VarRef pos ident
getLvalue (ELitInt pos _) = notLvalue pos "integer literal"
getLvalue (ELitBool pos _) = notLvalue pos "boolean literal"
getLvalue (EString pos _) = notLvalue pos "string literal"
getLvalue (ECoerce pos _ _) = notLvalue pos "coercion expression"
getLvalue (EApp pos _ _) = notLvalue pos "function application"
getLvalue (EClassMethod pos _ _ _) = notLvalue pos "method aplication"
getLvalue (EClassField pos expr ident) = do
    class_ <- getLvalue expr
    -- we don't have to check here whether such attribute exists, because creating Expr did that check already
    return $ ClassAttr pos class_ ident
getLvalue (EArrAt pos e1 e2) = do
    arr <- getLvalue e1
    return $ ArrRef pos arr e2
getLvalue (Neg pos _) = notLvalue pos "integer negation"
getLvalue (Not pos _) = notLvalue pos "logical negation"
getLvalue (EIntOp pos _ _ _) = notLvalue pos "operation on integers"
getLvalue (ERel pos _ _ _) = notLvalue pos "relation on integers"
getLvalue (EBoolOp pos _ _ _) = notLvalue pos "operation on booleans"

typeOfLvalue :: Lvalue -> Pass1M Type
typeOfLvalue (VarRef _ ident) = do
    (venv, _) <- get
    case M.lookup ident venv of
        Nothing -> undefined -- no such lvalue can be created
        Just (t, _) -> return t
typeOfLvalue (ClassAttr _ lval attrIdent) = do
    type_ <- typeOfLvalue lval
    case type_ of
        Class classIdent -> do
            (_, cenv) <- ask
            case M.lookup classIdent cenv of
                Nothing -> undefined -- no such lvalue can be created
                Just (attrs, _) -> do
                    case M.lookup attrIdent attrs of
                        Nothing -> undefined -- no such lvalue can be created
                        Just t -> return t
        _ -> undefined -- no such lvalue can be created
typeOfLvalue (ArrRef _ lval _) = do
    type_ <- typeOfLvalue lval
    return $ Array type_

pass1Expr :: (Abs.Expr Position) -> Pass1M Expr
pass1Expr (Abs.ENewArr pos t e) = do
    t' <- pass1Type t
    e' <- pass1Expr e
    typeE <- typeOfExpr e'
    case typeE of
        Int -> return $ ENewArr pos t' e'
        _ -> throwError (pos, "array size has to be an integer")
pass1Expr (Abs.ENewObj pos t) = ENewObj pos <$> pass1Type t
pass1Expr (Abs.EVar pos (Abs.Ident ident)) = do
    (venv, _) <- get
    case M.lookup ident venv of
        Nothing -> throwError (pos, "undeclared identifier " ++ ident)
        Just _ -> return $ EVar pos ident
pass1Expr (Abs.ELitInt pos n) = return $ ELitInt pos n
pass1Expr (Abs.ELitTrue pos) = return $ ELitBool pos True
pass1Expr (Abs.ELitFalse pos) = return $ ELitBool pos False
pass1Expr (Abs.EString pos s) = return $ EString pos s
pass1Expr (Abs.EBasicCoerce pos t e) = do
    let t' = pass1BuiltinType t
    e' <- pass1Expr e
    return $ ECoerce pos t' e'
pass1Expr (Abs.EBasicArrCoerce pos t e) = do
    let t' = pass1BuiltinType t
    e' <- pass1Expr e
    return $ ECoerce pos (Array t') e'
pass1Expr (Abs.EClassCoerce pos name e) = do
    case name of
        Abs.EVar _ (Abs.Ident className) -> do
            (_, cenv) <- ask
            case M.lookup className cenv of
                Nothing -> throwError (pos, "unknown type: " ++ className)
                Just _ -> ECoerce pos (Class className) <$> pass1Expr e
        _ -> throwError (pos, "expression cannot be used as a type")
pass1Expr (Abs.EClassArrCoerce pos name e) = do
    case name of
        Abs.EVar _ (Abs.Ident className) -> do
            (_, cenv) <- ask
            case M.lookup className cenv of
                Nothing -> throwError (pos, "unknown type: " ++ className)
                Just _ -> ECoerce pos (Array (Class className)) <$> pass1Expr e
        _ -> throwError (pos, "expression cannot be used as a type")
pass1Expr (Abs.EApp pos (Abs.Ident funIdent) args) = do
    (fenv, _) <- ask
    case M.lookup funIdent fenv of
        Nothing -> throwError (pos, "unknown function identifier")
        Just (_, argTypes) -> do
            args' <- mapM pass1Expr args
            argTypes' <- mapM typeOfExpr args'
            if argTypes == argTypes'
                then return $ EApp pos funIdent args'
                else throwError (pos, "incorrect types of arguments in call to function " ++ funIdent ++ ", expected " ++ show argTypes ++ ", got " ++ show argTypes')
pass1Expr (Abs.EClassMethod pos classExpr (Abs.Ident methodIdent) args) = do
    classExpr' <- pass1Expr classExpr
    classType <- typeOfExpr classExpr'
    case classType of
        Class classIdent -> do
            (_, cenv) <- ask
            case M.lookup classIdent cenv of
                Nothing -> throwError (pos, classIdent ++ " is not a correct class identifier")
                Just (_, methods) -> do
                    case M.lookup methodIdent methods of
                        Nothing -> throwError (pos, "class " ++ classIdent ++ " has no method " ++ methodIdent)
                        Just (_, argTypes) -> do
                            args' <- mapM pass1Expr args
                            argTypes' <- mapM typeOfExpr args'
                            if argTypes == argTypes'
                                then return $ EClassMethod pos classExpr' methodIdent args'
                                else throwError (pos, "incorrect types of arguments in call to method " ++ classIdent ++ "." ++ methodIdent)
        _ -> throwError (pos, "calling method on non-class type is forbidden")
pass1Expr (Abs.EClassField pos classExpr (Abs.Ident fieldIdent)) = do
    classExpr' <- pass1Expr classExpr
    classType <- typeOfExpr classExpr'
    case classType of
        Class classIdent -> do
            (_, cenv) <- ask
            case M.lookup classIdent cenv of
                Nothing -> throwError (pos, classIdent ++ " is not a correct class identifier")
                Just (fields, _) -> do
                    case M.lookup fieldIdent fields of
                        Nothing -> throwError (pos, "class " ++ classIdent ++ " has no field " ++ fieldIdent)
                        Just _ -> do
                            return $ EClassField pos classExpr' fieldIdent
        _ -> throwError (pos, "calling method on non-class type is forbidden")
pass1Expr (Abs.EArrAt pos arrExpr indexExp) = do
    arrExp' <- pass1Expr arrExpr
    arrType <- typeOfExpr arrExp'
    indexExp' <- pass1Expr indexExp
    indexType <- typeOfExpr indexExp'
    case indexType of
        Int -> do
            case arrType of
                Array _ -> return $ EArrAt pos arrExp' indexExp'
                _ -> throwError (pos, "cannot index non-array type")
        _ -> throwError (pos, "array index must be an integer")
pass1Expr (Abs.Neg pos expr) = do
    expr' <- pass1Expr expr
    t <- typeOfExpr expr'
    case t of
        Int -> return $ Neg pos expr'
        _ -> throwError (pos, "type mismatch - cannot perform integer negation on non-integer expressions")
pass1Expr (Abs.Not pos expr) = do
    expr' <- pass1Expr expr
    t <- typeOfExpr expr'
    case t of
        Bool -> return $ Not pos expr'
        _ -> throwError (pos, "type mismatch - cannot perform boolean negation on non-boolean expressions")
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
    typee1 <- typeOfExpr e1'
    e2' <- pass1Expr e2
    typee2 <- typeOfExpr e2'
    case (typee1, typee2) of
        (Int, Int) -> do
            let createEMul f op = do {
                case (e1', e2') of
                    (ELitInt _ n, ELitInt _ m) -> return $ ELitInt pos (f n m)
                    _ -> return $ EIntOp pos e1' op e2'
            }
            case mulop of
                Abs.Times _ -> createEMul (*) Mul
                Abs.Div _ -> checkIf0 e2' "division" *> createEMul div Div
                Abs.Mod _ -> checkIf0 e2' "modulo" *> createEMul mod Mod
        _ -> throwError (getPosMul mulop, "type mismatch - both operands should be integers")
pass1Expr (Abs.EAdd pos e1 addop e2) =
    let
        getPosAdd :: Abs.AddOp Position -> Position
        getPosAdd (Abs.Plus p) = p
        getPosAdd (Abs.Minus p) = p
    in do
    e1' <- pass1Expr e1
    typee1 <- typeOfExpr e1'
    e2' <- pass1Expr e2
    typee2 <- typeOfExpr e2'
    case (typee1, typee2) of
        (Int, Int) -> do
            let createEAdd f op = do {
                case (e1', e2') of
                    (ELitInt _ n, ELitInt _ m) -> return $ ELitInt pos (f n m)
                    _ -> return $ EIntOp pos e1' op e2'
            }
            case addop of
                Abs.Plus _ -> createEAdd (+) Add
                Abs.Minus _ -> createEAdd (-) Sub
        (String_, String_) -> do
            case addop of
                Abs.Minus _ ->  throwError (getPosAdd addop, "type mismatch - both operands should be integers")
                Abs.Plus _ -> do
                    case (e1', e2') of
                        (EString _ n, EString _ m) -> return $ EString pos (n ++ m)
                        _ -> return $ EIntOp pos e1' Add e2'
        _ -> throwError (getPosAdd addop, "type mismatch - both operands should be integers")
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
    typee1 <- typeOfExpr e1'
    e2' <- pass1Expr e2
    typee2 <- typeOfExpr e2'
    let createERelInt f op = do {
        case (e1', e2') of
            (ELitInt _ n, ELitInt _ m) -> return $ ELitBool pos (f n m)
            _ -> return $ ERel pos e1' op e2'
    }
    let createERelString f op = do {
        case (e1', e2') of
            (EString _ n, EString _ m) -> return $ ELitBool pos (f n m)
            _ -> return $ ERel pos e1' op e2'
    }
    let createERelBool f op = do {
        case (e1', e2') of
            (ELitBool _ n, ELitBool _ m) -> return $ ELitBool pos (f n m)
            _ -> return $ ERel pos e1' op e2'
    }
    let mismatchIntegers = throwError (getPosRel relop, "type mismatch - both operands should be integers")
    let mismatchSameType = throwError (getPosRel relop, "type mismatch - both operands should be of the same type")
    case relop of
        Abs.LTH _ -> do
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (<) Lth
                _ -> mismatchIntegers
        Abs.LE _ -> do
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (<=) Lth
                _ -> mismatchIntegers
        Abs.GTH _ -> do
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (>) Lth
                _ -> mismatchIntegers
        Abs.GE _ -> do
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (>=) Lth
                _ -> mismatchIntegers
        Abs.EQU _ -> do
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (==) Equ
                (String_, String_) -> createERelString (==) Equ
                (Bool, Bool) -> createERelBool (==) Equ
                _ -> mismatchSameType
        Abs.NE _ -> do
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (/=) Equ
                (String_, String_) -> createERelString (/=) Equ
                (Bool, Bool) -> createERelBool (/=) Equ
                _ -> mismatchSameType
pass1Expr (Abs.EAnd pos e1 e2) = do
    e1' <- pass1Expr e1
    typee1 <- typeOfExpr e1'
    e2' <- pass1Expr e2
    typee2 <- typeOfExpr e2'
    let createEBool f op = do {
        case (e1', e2') of
            (ELitBool _ n, ELitBool _ m) -> return $ ELitBool pos (f n m)
            _ -> return $ EBoolOp pos e1' op e2'
    }
    case (typee1, typee2) of
        (Bool, Bool) -> createEBool (&&) And
        _ -> throwError (pos, "type mismatch - both operands should be booleans")
pass1Expr (Abs.EOr pos e1 e2) = do
    e1' <- pass1Expr e1
    typee1 <- typeOfExpr e1'
    e2' <- pass1Expr e2
    typee2 <- typeOfExpr e2'
    let createEBool f op = do {
        case (e1', e2') of
            (ELitBool _ n, ELitBool _ m) -> return $ ELitBool pos (f n m)
            _ -> return $ EBoolOp pos e1' op e2'
    }
    case (typee1, typee2) of
        (Bool, Bool) -> createEBool (||) Or
        _ -> throwError (pos, "type mismatch - both operands should be booleans")

typeOfExpr :: Expr -> Pass1M Type
typeOfExpr (ENewArr _ t _) = return $ Array t
typeOfExpr (ENewObj _ t) = return t
typeOfExpr (EVar _ ident) = do
    (venv, _) <- get
    case M.lookup ident venv of
        Nothing -> undefined -- no such expr can be created
        Just (t, _) -> return t
typeOfExpr (ELitInt _ _) = return $ Int
typeOfExpr (ELitBool _ _) = return $ Bool
typeOfExpr (EString _ _) = return $ String_
typeOfExpr (ECoerce _ t _) = return t
typeOfExpr (EApp _ ident _) = do
    (fenv, _) <- ask
    case M.lookup ident fenv of
        Nothing -> undefined
        Just (t, _) -> return t
typeOfExpr (EClassMethod _ e methodIdent _) = do
    t <- typeOfExpr e
    case t of
        Class classIdent -> do
            (_, cenv) <- ask
            case M.lookup classIdent cenv of
                Nothing -> undefined
                Just (_, methods) -> do
                    case M.lookup methodIdent methods of
                        Nothing -> undefined
                        Just (retT, _) -> return retT
        _ -> undefined
typeOfExpr (EClassField _ e fieldIdent) = do
    t <- typeOfExpr e
    case t of
        Class classIdent -> do
            (_, cenv) <- ask
            case M.lookup classIdent cenv of
                Nothing -> undefined
                Just (fields, _) -> do
                    case M.lookup fieldIdent fields of
                        Nothing -> undefined
                        Just retT -> return retT
        _ -> undefined
typeOfExpr (EArrAt _ e _) = do
    t <- typeOfExpr e
    case t of
        Array retT -> return retT
        _ -> undefined
typeOfExpr (Neg _ _ ) = return Int
typeOfExpr (Not _ _) = return Bool
typeOfExpr (EIntOp _ e Add _) = typeOfExpr e
typeOfExpr (EIntOp _ _ _ _) = return Int
typeOfExpr (ERel _ _ _ _) = return Bool
typeOfExpr (EBoolOp _ _ _ _) = return Bool

-- first pass through ast, frontend
pass1 :: (Abs.Program Position) -> Pass1M Program
pass1 (Abs.Program p tlds) =
    let
        initialFenv = M.fromList
            [("printInt", (Void, [Int])),
            ("printString", (Void, [String_])),
            ("error", (Void, [])),
            ("readInt", (Int, [])),
            ("readString", (String_, []))]
    in
    let
        helper fdefs (Abs.FnDef pos (Abs.FunDef _ t (Abs.Ident ident) args _)) = do
            t' <- pass1Type t
            args' <- mapM (\(Abs.Arg _ type_ _) -> pass1Type type_) args
            case M.lookup ident fdefs of
                Nothing -> return $ M.insert ident (t', args') fdefs
                Just _ -> throwError (pos, "function " ++ ident ++ " defined twice")
        helper fdefs (Abs.ClassDef _ _ _) = return fdefs
        helper fdefs (Abs.ClassExtDef _ _ _ _) = return fdefs
        helper2 (pos, acc) (Abs.FnDef _ fundef@(Abs.FunDef currentPos _ (Abs.Ident name) _ _)) =
            if name == "main"
                then (currentPos, fundef : acc)
                else (pos, fundef : acc)
        helper2 acc (Abs.ClassDef _ _ _) = acc
        helper2 acc (Abs.ClassExtDef _ _ _ _) = acc
    in do
        fenv <- foldM helper initialFenv tlds
        let (mainPos, fundefs) = foldl helper2 (Nothing, []) tlds
        case M.lookup "main" fenv of
            Nothing -> throwError (p, "no main function specified")
            Just (retType, argTypes) -> do
                if retType /= Int || argTypes /= []
                    then throwError (mainPos, "Incorrect type of main function: its signature should be `int main()`")
                    else return ()
        fundefs' <- local (\_ -> (fenv, M.empty)) (mapM pass1FunDef fundefs)
        return $ Program p [] fundefs'

