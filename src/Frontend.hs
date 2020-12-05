{-# Options -Wall -Wname-shadowing #-}

module Frontend where

import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader

import qualified Parsing.AbsLatte as Abs

type Position = Maybe (Int, Int)
type Ident = String
data Type
    = Int Position
    | Bool_ Position
    | String_ Position
    | Class Ident Position
    | Array Position Type
data Program = Program Position [ClassDef] [FunDef]
data ClassDef = ClassDef Position Ident (Maybe Ident) [ClassBody]
data ClassBody = AttrVar Position Type Ident | AttrFun Position FunDef
data FunDef = FunDef Position Type Ident [Arg] Block
type Arg = (Type, Ident)
data Block = Block Position [Stmt]
data Stmt
    = Empty Position
    | BStmt Position Block
    | Decl Position Type [Item]
    | Ass Position Expr Expr
    | Incr Position Expr
    | Decr Position Expr
    | Ret (Maybe Expr)
    | Cond Position Expr Stmt (Maybe Stmt)
    | While Position Expr Stmt
    | SExp Position Expr
    | For Position Ident Expr Stmt
data Item = Item Ident (Maybe Expr)
data Expr
    = ENewArr Position Type Expr
    | ENewObj Position Ident
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

data IntOp = Mul | Div | Add | Sub | Mod
data IntRel = Lth | Le | Gth | Ge | Equ | Neq
data BoolOp = Or | And

type Venv = M.Map Ident Type -- variable env
type Fenv = M.Map Ident (Type, [Type]) -- function env
type Cenv = M.Map Ident ClassDef -- classes env
type Pass1M = ExceptT (Position, String) (StateT Venv (Reader (Fenv, Cenv)))

-- first pass through ast, frontend
pass1 :: (Abs.Program (Maybe (Int, Int))) -> Pass1M Program
pass1 (Abs.Program p tlds) =
    let
        helper (fdefs, cdefs, cedefs) (Abs.FnDef pos fundef) = ((pos, fundef) : fdefs, cdefs, cedefs)
        helper (fdefs, cdefs, cedefs) (Abs.ClassDef pos ident body) = (fdefs, (pos, ident, body) : cdefs, cedefs)
        helper (fdefs, cdefs, cedefs) (Abs.ClassExtDef pos ident ident' body) = (fdefs, cdefs, (pos, ident, ident', body) : cedefs)
    in let
        (fundefs, classdefs, classextdefs) = foldl helper ([], [], []) tlds
    in if L.length fundefs > 0 || L.length classdefs > 0 || L.length classextdefs > 0 then return (Program p [] []) else return (Program (Just (-1, -1)) [] [])


