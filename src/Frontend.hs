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

data Program = Program Position [ClassDef] [FunDef] deriving Show
data ClassDef = ClassDef Position Ident (Maybe Ident) [ClassBody] deriving Show
data ClassBody = AttrVar Position Type Ident | AttrFun Position FunDef deriving Show
data FunDef = FunDef Position Type Ident [Arg] Block deriving Show
type Arg = (Position, Type, Ident)
data Block = Block Position [Stmt] deriving Show
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
    deriving Show
data Item = Item Position Ident (Maybe Expr) deriving Show
-- position and type are kept for every nonobvious expression and lvalue
data Expr
    = ENewArr Type Position Type Expr
    | ENewObj Position Type
    | EVar Type Position Ident
    | ELitInt Position Integer
    | ELitBool Position Bool
    | EString Position String
    | ECoerce Position Type Expr
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
type Venv = M.Map Ident (Type, Depth) -- variable env
type Fenv = M.Map Ident (Type, [Type]) -- function env
type Cenv = M.Map Ident (M.Map Ident Type, M.Map Ident (Type, [Type])) -- classes env
type Pass1M = ReaderT (Fenv, Cenv, Type) (StateT (Venv, Depth) (Except (Position, String)))

data ReturnState = RSUnknown | RSNever | RSYes deriving Eq

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
        Incr{} -> RSUnknown
        Decr{} -> RSUnknown
        Ret{} -> RSYes
        Cond _ _ s1 (Just s2) ->
            let
                res1 = checkReturnStmt s1
                res2 = checkReturnStmt s2
            in
            if res1 == res2
                then res1
                else
                    if (res1 == RSYes && res2 == RSNever) || (res1 == RSNever && res2 == RSYes)
                        then RSYes
                        else RSUnknown
        Cond{} -> RSUnknown
        -- allow using while (true) without return
        While _ (ELitBool _ True) _ -> RSNever
        While{} -> RSUnknown
        SExp _ (EApp _ _ "error" _) -> RSNever
        SExp{} -> RSUnknown
        For{} -> RSUnknown

pass1BuiltinType :: Abs.BuiltinType Position -> Type
pass1BuiltinType (Abs.Int _) = Int
pass1BuiltinType (Abs.Str _) = String_
pass1BuiltinType (Abs.Bool _) = Bool
pass1BuiltinType (Abs.Void _) = Void

pass1ClassType :: String -> Position -> Pass1M Type
pass1ClassType ident pos = do
    (_, cenv, _) <- ask
    if M.member ident cenv
        then return (Array (Class ident))
        else throwError (pos, "Undeclared type: " ++ ident)

pass1ArrayType :: Abs.ArrayType Position -> Pass1M Type
pass1ArrayType (Abs.BuiltinArr _ type_) = return $ Array (pass1BuiltinType type_)
pass1ArrayType (Abs.UserArr pos (Abs.Ident ident)) = pass1ClassType ident pos

pass1Type :: Abs.Type Position -> Pass1M Type
pass1Type (Abs.BltinType _ t) = return (pass1BuiltinType t)
pass1Type (Abs.ArrType _ t) = pass1ArrayType t
pass1Type (Abs.UserType pos (Abs.Ident ident)) = pass1ClassType ident pos

pass1FunDef :: Abs.FunDef Position -> Pass1M FunDef
pass1FunDef (Abs.FunDef pos t (Abs.Ident name) args body) = do
    t' <- pass1Type t
    args' <- mapM pass1Arg args
    (oldVenv, depth) <- get
    let envModification = M.fromList (map (\(_, type_, ident) -> (ident, (type_, depth))) args')
    let newVenv = M.union envModification oldVenv
    put (newVenv, depth + 1)
    body' <- local (\(fenv, cenv, _) -> (fenv, cenv, t')) (pass1Block body)
    put (oldVenv, depth)
    if checkReturnBlock body' /= RSUnknown || t' == Void
        then return $ FunDef pos t' name args' body'
        else throwError (pos, "function returning non-void doesn't have a return")

pass1Arg :: Abs.Arg Position -> Pass1M Arg
pass1Arg (Abs.Arg pos t (Abs.Ident ident)) = do
    t' <- pass1Type t
    return (pos, t', ident)

pass1Block :: Abs.Block Position -> Pass1M Block
pass1Block (Abs.Block pos stmts) = do
    (oldVenv, depth) <- get
    put (oldVenv, depth + 1)
    stmts' <- mapM pass1Stmt stmts
    put (oldVenv, depth)
    return $ Block pos stmts'

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
    if typeOfLvalue lval == typeOfExpr expr
        then return $ Ass pos lval expr
        else throwError (pos, "cannot assign expression of type " ++ show (typeOfExpr expr) ++ " to variable of type " ++ show (typeOfLvalue lval))
pass1Stmt (Abs.Incr pos expr) = Incr pos <$> (pass1Expr expr >>= getLvalue)
pass1Stmt (Abs.Decr pos expr) = Decr pos <$> (pass1Expr expr >>= getLvalue)
pass1Stmt (Abs.Ret pos expr) = do
    expr' <- pass1Expr expr
    (_, _, retType) <- ask
    if typeOfExpr expr' /= retType
        then throwError (pos, "cannot return something of type " ++ show (typeOfExpr expr') ++ " from a function returning " ++ show retType)
        else return $ Ret pos (Just expr')
pass1Stmt (Abs.VRet pos) = do
    (_, _, retType) <- ask
    if retType /= Void
        then throwError (pos, "cannot have empty return in function returning " ++ show retType)
        else return $ Ret pos Nothing
pass1Stmt (Abs.Cond pos cond body) = do
    cond' <- pass1Expr cond
    body' <- pass1Stmt body
    case typeOfExpr cond' of
        Bool ->
            case cond' of
                ELitBool _ True -> return body'
                ELitBool _ False -> return $ Empty pos
                _ -> return $ Cond pos cond' body' Nothing
        _ -> throwError (pos, "condition in if statement must be boolean")
pass1Stmt (Abs.CondElse pos cond bodyIf bodyElse) = do
    cond' <- pass1Expr cond
    bodyIf' <- pass1Stmt bodyIf
    bodyElse' <- pass1Stmt bodyElse
    case typeOfExpr cond' of
        Bool ->
            case cond' of
                ELitBool _ True -> return bodyIf'
                ELitBool _ False -> return bodyElse'
                _ -> return $ Cond pos cond' bodyIf' (Just bodyElse')
        _ -> throwError (pos, "condition in if statement must be boolean")
pass1Stmt (Abs.While pos cond body) = do
    cond' <- pass1Expr cond
    body' <- pass1Stmt body
    case typeOfExpr cond' of
        Bool ->
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
    case typeOfExpr iter' of
        Array iterType -> if t' == iterType
            then do
                (oldVenv, depth) <- get
                put (M.insert ident (iterType, depth) oldVenv, depth + 1)
                body' <- pass1Stmt body
                put (oldVenv, depth)
                return (For pos ident iter' body')
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
pass1Item :: Type -> Abs.Item Position -> Pass1M Item
pass1Item t (Abs.NoInit pos (Abs.Ident ident)) = do
    checkdecl pos ident t
    return $ Item pos ident Nothing
pass1Item t (Abs.Init pos (Abs.Ident ident) expr) = do
    expr' <- pass1Expr expr
    if t /= typeOfExpr expr'
        then throwError (pos, "Cannot assign value of type " ++ show (typeOfExpr expr') ++ " to variable of type " ++ show t)
        else do
            checkdecl pos ident t
            return $ Item pos ident $ Just expr'

notLvalue :: Position -> String -> Pass1M a
notLvalue p s = throwError (p, s ++ " cannot be used as lvalue")

getLvalue :: Expr -> Pass1M Lvalue
getLvalue (ENewArr _ pos _ _) = notLvalue pos "array declaration"
getLvalue (ENewObj pos _ ) = notLvalue pos "object declaration"
getLvalue (EVar t pos ident) = return $ VarRef t pos ident
getLvalue (ELitInt pos _) = notLvalue pos "integer literal"
getLvalue (ELitBool pos _) = notLvalue pos "boolean literal"
getLvalue (EString pos _) = notLvalue pos "string literal"
getLvalue (ECoerce pos _ _) = notLvalue pos "coercion expression"
getLvalue (EApp _ pos _ _) = notLvalue pos "function application"
getLvalue (EClassMethod _ pos _ _ _) = notLvalue pos "method aplication"
getLvalue (EClassField t pos expr ident) = do
    class_ <- getLvalue expr
    -- we don't have to check here whether such attribute exists, because creating Expr did that check already
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

pass1Expr :: Abs.Expr Position -> Pass1M Expr
pass1Expr (Abs.ENewArr pos t e) = do
    t' <- pass1Type t
    e' <- pass1Expr e
    case typeOfExpr e' of
        Int -> return $ ENewArr (Array t') pos t' e'
        _ -> throwError (pos, "array size has to be an integer")
pass1Expr (Abs.ENewObj pos t) = ENewObj pos <$> pass1Type t
pass1Expr (Abs.EVar pos (Abs.Ident ident)) = do
    (venv, _) <- get
    case M.lookup ident venv of
        Nothing -> throwError (pos, "undeclared identifier " ++ ident)
        Just (t, _) -> return $ EVar t pos ident
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
pass1Expr (Abs.EClassCoerce pos name e) =
    case name of
        Abs.EVar _ (Abs.Ident className) -> do
            (_, cenv, _) <- ask
            case M.lookup className cenv of
                Nothing -> throwError (pos, "unknown type: " ++ className)
                Just _ -> ECoerce pos (Class className) <$> pass1Expr e
        _ -> throwError (pos, "expression cannot be used as a type")
pass1Expr (Abs.EClassArrCoerce pos name e) =
    case name of
        Abs.EVar _ (Abs.Ident className) -> do
            (_, cenv, _) <- ask
            case M.lookup className cenv of
                Nothing -> throwError (pos, "unknown type: " ++ className)
                Just _ -> ECoerce pos (Array (Class className)) <$> pass1Expr e
        _ -> throwError (pos, "expression cannot be used as a type")
pass1Expr (Abs.EApp pos (Abs.Ident funIdent) args) = do
    (fenv, _, _) <- ask
    case M.lookup funIdent fenv of
        Nothing -> throwError (pos, "unknown function identifier")
        Just (retType, argTypes) -> do
            args' <- mapM pass1Expr args
            let argTypes' = map typeOfExpr args'
            if argTypes == argTypes'
                then return $ EApp retType pos funIdent args'
                else throwError (pos, "incorrect types of arguments in call to function " ++ funIdent ++ ", expected " ++ show argTypes ++ ", got " ++ show argTypes')
pass1Expr (Abs.EClassMethod pos classExpr (Abs.Ident methodIdent) args) = do
    classExpr' <- pass1Expr classExpr
    case typeOfExpr classExpr' of
        Class classIdent -> do
            (_, cenv, _) <- ask
            case M.lookup classIdent cenv of
                Nothing -> throwError (pos, classIdent ++ " is not a correct class identifier")
                Just (_, methods) ->
                    case M.lookup methodIdent methods of
                        Nothing -> throwError (pos, "class " ++ classIdent ++ " has no method " ++ methodIdent)
                        Just (retType, argTypes) -> do
                            args' <- mapM pass1Expr args
                            let argTypes' = map typeOfExpr args'
                            if argTypes == argTypes'
                                then return $ EClassMethod retType pos classExpr' methodIdent args'
                                else throwError (pos, "incorrect types of arguments in call to method " ++ classIdent ++ "." ++ methodIdent ++ ", expected " ++ show argTypes ++ ", got " ++ show argTypes')
        _ -> throwError (pos, "calling method on non-class type is forbidden")
pass1Expr (Abs.EClassField pos classExpr (Abs.Ident fieldIdent)) = do
    classExpr' <- pass1Expr classExpr
    case typeOfExpr classExpr' of
        Class classIdent -> do
            (_, cenv, _) <- ask
            case M.lookup classIdent cenv of
                Nothing -> throwError (pos, classIdent ++ " is not a correct class identifier")
                Just (fields, _) ->
                    case M.lookup fieldIdent fields of
                        Nothing -> throwError (pos, "class " ++ classIdent ++ " has no field " ++ fieldIdent)
                        Just fieldType ->
                            return $ EClassField fieldType pos classExpr' fieldIdent
        Array _ -> if fieldIdent /= "length"
            then throwError (pos, "array has no member " ++ fieldIdent ++ ", oly length")
            else return $ EClassField Int pos classExpr' fieldIdent
        _ -> throwError (pos, "accessing members on non-class type " ++ show (typeOfExpr classExpr') ++ " is forbidden")
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
        Int -> return $ Neg pos expr'
        _ -> throwError (pos, "type mismatch - cannot perform integer negation on non-integer expressions")
pass1Expr (Abs.Not pos expr) = do
    expr' <- pass1Expr expr
    case typeOfExpr expr' of
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
    e2' <- pass1Expr e2
    case (typeOfExpr e1', typeOfExpr e2') of
        (Int, Int) -> do
            let createEMul f op = do {
                case (e1', e2') of
                    (ELitInt _ n, ELitInt _ m) -> return $ ELitInt pos (f n m)
                    _ -> return $ EIntOp Int pos e1' op e2'
            }
            case mulop of
                Abs.Times _ -> optimizeBinOp <$> createEMul (*) Mul
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
    e2' <- pass1Expr e2
    case (typeOfExpr e1', typeOfExpr e2') of
        (Int, Int) -> do
            let createEAdd f op = do {
                case (e1', e2', op) of
                    (ELitInt _ n, ELitInt _ m, _) -> return $ ELitInt pos (f n m)
                    _ -> return $ EIntOp Int pos e1' op e2'
            }
            case addop of
                Abs.Plus _ -> optimizeBinOp <$> createEAdd (+) Add
                Abs.Minus _ -> createEAdd (-) Sub
        (String_, String_) ->
            case addop of
                Abs.Minus _ ->  throwError (getPosAdd addop, "type mismatch - both operands should be integers")
                Abs.Plus _ -> do
                    case (e1', e2') of
                        (EString _ n, EString _ m) -> return $ EString pos (n ++ m)
                        _ -> return $ EIntOp String_ pos e1' Add e2'
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
    let typee1 = typeOfExpr e1'
    e2' <- pass1Expr e2
    let typee2 = typeOfExpr e2'
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
        Abs.LTH _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (<) Lth
                _ -> mismatchIntegers
        Abs.LE _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (<=) Lth
                _ -> mismatchIntegers
        Abs.GTH _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (>) Lth
                _ -> mismatchIntegers
        Abs.GE _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (>=) Lth
                _ -> mismatchIntegers
        Abs.EQU _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (==) Equ
                (String_, String_) -> createERelString (==) Equ
                (Bool, Bool) -> createERelBool (==) Equ
                _ -> mismatchSameType
        Abs.NE _ ->
            case (typee1, typee2) of
                (Int, Int) -> createERelInt (/=) Equ
                (String_, String_) -> createERelString (/=) Equ
                (Bool, Bool) -> createERelBool (/=) Equ
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
            _ -> return $ optimizeBinOp $ EBoolOp pos e1' op e2'
    }
    case (typeOfExpr e1', typeOfExpr e2') of
        (Bool, Bool) -> createEBool
        _ -> throwError (pos, "type mismatch - both operands should be booleans")

optimizeBinOp :: Expr -> Expr
optimizeBinOp (EIntOp Int p (EIntOp _ _ (ELitInt p' n) Add expr) Add (ELitInt _ m)) =
    EIntOp Int p (ELitInt p' (n + m)) Add expr
optimizeBinOp (EIntOp Int p (EIntOp _ _ expr Add (ELitInt p' n)) Add (ELitInt _ m)) =
    EIntOp Int p (ELitInt p' (n + m)) Add expr
optimizeBinOp (EIntOp Int p (ELitInt p' m) Add (EIntOp _ _ (ELitInt _ n) Add expr)) =
    EIntOp Int p (ELitInt p' (n + m)) Add expr
optimizeBinOp (EIntOp Int p (ELitInt p' m) Add (EIntOp _ _ expr Add (ELitInt _ n))) =
    EIntOp Int p (ELitInt p' (n + m)) Add expr
optimizeBinOp (EIntOp Int p (EIntOp _ _ (ELitInt p' n) Mul expr) Mul (ELitInt _ m)) =
    EIntOp Int p (ELitInt p' (n * m)) Mul expr
optimizeBinOp (EIntOp Int p (EIntOp _ _ expr Mul (ELitInt p' n)) Mul (ELitInt _ m)) =
    EIntOp Int p (ELitInt p' (n * m)) Mul expr
optimizeBinOp (EIntOp Int p (ELitInt p' m) Mul (EIntOp _ _ (ELitInt _ n) Mul expr)) =
    EIntOp Int p (ELitInt p' (n * m)) Mul expr
optimizeBinOp (EIntOp Int p (ELitInt p' m) Mul (EIntOp _ _ expr Mul (ELitInt _ n))) =
    EIntOp Int p (ELitInt p' (n * m)) Mul expr
optimizeBinOp (EBoolOp _ (ELitBool _ True) And expr) = expr
optimizeBinOp (EBoolOp _ expr And (ELitBool _ True)) = expr
optimizeBinOp (EBoolOp p (ELitBool _ True) Or _) = ELitBool p True
optimizeBinOp (EBoolOp _ (ELitBool _ False) Or expr) = expr
optimizeBinOp (EBoolOp _ expr Or (ELitBool _ False)) = expr
optimizeBinOp (EBoolOp p (ELitBool _ False) And _) = ELitBool p False
optimizeBinOp expr = expr

typeOfExpr :: Expr -> Type
typeOfExpr (ENewArr t _ _ _) = t
typeOfExpr (ENewObj _ t) = t
typeOfExpr (EVar t _ _) = t
typeOfExpr (ELitInt _ _) = Int
typeOfExpr (ELitBool _ _) = Bool
typeOfExpr (EString _ _) = String_
typeOfExpr (ECoerce _ t _) = t
typeOfExpr (EApp t _ _ _) = t
typeOfExpr (EClassMethod t _ _ _ _) = t
typeOfExpr (EClassField t _ _ _) = t
typeOfExpr (EArrAt t _ _ _) = t
typeOfExpr (Neg _ _ ) = Int
typeOfExpr (Not _ _) = Bool
typeOfExpr (EIntOp t _ _ _ _) = t
typeOfExpr ERel{} = Bool
typeOfExpr EBoolOp{} = Bool

-- first pass through ast, frontend
pass1 :: Abs.Program Position -> Pass1M Program
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
        helper fdefs Abs.ClassDef{} = return fdefs
        helper fdefs Abs.ClassExtDef{} = return fdefs
        helper2 (pos, fdefs, cdefs, cedefs) (Abs.FnDef _ fundef@(Abs.FunDef currentPos _ (Abs.Ident name) _ _)) =
            if name == "main"
                then (currentPos, fundef : fdefs, cdefs, cedefs)
                else (pos, fundef : fdefs, cdefs, cedefs)
        helper2 (pos, fdefs, cdefs, cedefs) (Abs.ClassDef _ (Abs.Ident ident) cbody) = (pos, fdefs, (ident, cbody) : cdefs, cedefs)
        helper2 (pos, fdefs, cdefs, cedefs) cedef@Abs.ClassExtDef{} = (pos, fdefs, cdefs, cedef : cedefs)
    in do
        fenv <- foldM helper initialFenv tlds
        let (mainPos, fundefs, cdefs, cedefs) = foldl helper2 (Nothing, [], [], []) tlds
        case M.lookup "main" fenv of
            Nothing -> throwError (p, "no main function specified")
            Just (retType, argTypes) ->
                when (retType /= Int || argTypes /= [])
                    (throwError (mainPos, "Incorrect type of main function: its signature should be `int main()`"))
        when (not (null cdefs) || not (null cedefs))
            (throwError (Nothing, "Detected classes declarations in the program, those are not supported yet"))
        fundefs' <- local (const (fenv, M.empty, Void)) (mapM pass1FunDef fundefs)
        return $ Program p [] fundefs'

