module Evalgram where

import Absgram
import Data.Map as M
import Control.Monad.State
import Data.Maybe

data Value = I Integer | B Bool | Ar Type [Value] | Rc RecName [(Type, Value)] deriving (Eq,Ord,Show)


-- data Type = TInt | TBool | TArr Type | TRec

-- data Val = Int | Bool deriving (Eq,Ord,Show)

type Val = Int

type Loc = Int 

data Obj = Fun StmtB | Var Loc deriving (Eq,Ord,Show)

type Env = M.Map LIdent Obj 

type Store = (M.Map Loc (Type, Value), Loc)

data PState = PS (Env, Store) deriving (Eq,Ord,Show)

clearEnv :: Env
clearEnv = M.empty

clearStore :: Store
clearStore = (M.empty, 0)

initialState :: PState
initialState = PS (clearEnv, clearStore)

addVar lident loc = do
	PS (env, s) <- get
	put $ PS (M.insert lident (Var loc) env, s)

getLoc lident = do
	PS (env, s) <- get
	case M.lookup lident env of
		Just (Fun _) -> fail "Expectec variable, not function name"
		Just (Var l) -> return $ l
		Nothing -> fail "Undefined variable"

alloc typ = do
	PS (e, (m, loc)) <- get
	put $ PS (e, (M.insert (loc + 1) (typ, defaultValue typ) m, loc + 1))
	return $ loc + 1


defaultValue Tint = I 0
defaultValue Tbool = B False
defaultValue (Tarr type_) = Ar type_ []


typeMatches Tint (I _) = True
typeMatches Tbool (B _) = True
typeMatches (Tarr typ1) (Ar typ2 _) = typ1 == typ2
typeMatches (Trec rName1) (Rc rName2 _) = rName1 == rName2
typeMatches _ _ = False


toType (I _) = Tint
toType (B _) = Tbool
toType (Ar typ _) = (Tarr typ)
toType (Rc rName _) = (Trec rName)

valueToBool (B b) = b
valueToBool _ = False

valueToInt (I i) = i
valueToInt _ = 0

assign val loc = do
	PS (e, (store, l)) <- get
	case M.lookup loc store of
		Just (typ, _) -> if (typeMatches typ val) then
				put $ PS (e, (M.insert loc (typ, val) store, l))
			else
				fail $ "Expected " ++ (show typ) ++ ", got " ++ (show (toType val)) ++ ".\n"
		Nothing -> fail "Location unalloced"

checkType e1 e2 type_ = (toType e1) == type_ && (toType e2) == type_ 
checkType_ e1 e2 = (toType e1) == (toType e2)

typeMissmatch t1 t2 type_ = "Could not match type " ++ (show t1) ++ " or " ++ (show t2) ++ " with type " ++ (show type_) ++ ".\n"
typeMissmatch_ t1 t2 = "Could not match type " ++ (show t1) ++ " and " ++ (show t2) ++ ".\n"
typeMissmatchS t typ = "Could not match type " ++ (show t) ++ " with " ++ (show typ) ++ ".\n"

evalProgram p = execState (evalProg p) initialState

evalProg (Prog (d:dl)) = do
	evalDecl d

evalDecl (Dstmt stmtB) = do
	evalStmtB stmtB

evalStmtB (Slist sList) = do
	evalStmtL sList

evalStmtL (Slst (s:sl)) = do
	evalStmt s

-- evalDecl (env, store) (Dstmt stmtB) = return $ evalStmtB (Just (env, store)) stmtB
-- evalDecl (env, store) (Dfun type_ ident pDecl stmtB) = return $ error "pepe"
-- evalDecl (env, store) (Dproc ident pDecl stmtB) = return $ error "pepe"
-- evalDecl (env, store) (Drec recName vDecl) = return $ error "pepe"

-- evalStmtB (env, store) (Slist sList) = return $ evalStmtL (Just (env, store)) sList
-- evalStmtB (env, store) (Sblock stmtList) = return $ foldM evalStmtL (Just (env, store)) stmtList 
-- 
-- evalStmtL (env, store) (Slst sList) = return $ foldM evalStmt (Just (env, store)) sList

evalStmt (Sdecl sDecl) = do
	evalSDecl sDecl

evalStmt (Sass lident expr) = do
	v <- evalExpr expr
	loc <- getLoc lident
	assign v loc

evalSDecl (Svar vDecl) = do
	evalVDecl vDecl

evalVDecl (VDcl typ lident) = do
	loc <- alloc typ
	addVar lident loc

--  EXPRESIONS --

--    Edarr [Exp]
evalExpr (Eor e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType v1 v2 Tbool) then
		return $ B ((valueToBool v1) || (valueToBool v2))
	else
		fail $ typeMissmatch v1 v2 Tbool

evalExpr (Eand e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType v1 v2 Tbool) then
		return $ B ((valueToBool v1) && (valueToBool v2))
	else
		fail $ typeMissmatch v1 v2 Tbool

evalExpr (Eeq e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType_ v1 v2) then
		return $ B (v1 == v2)
	else
		fail $ typeMissmatch_ v1 v2

evalExpr (Edif e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType_ v1 v2) then
		return $ B (v1 /= v2)
	else
		fail $ typeMissmatch_ v1 v2

evalExpr (Egt e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType v1 v2 Tint) then
		return $ B ((valueToInt v1) > (valueToInt v2))
	else
		fail $ typeMissmatch v1 v2 Tint

evalExpr (Egte e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType v1 v2 Tint) then
		return $ B ((valueToInt v1) >= (valueToInt v2))
	else
		fail $ typeMissmatch v1 v2 Tint

evalExpr (Elt e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType v1 v2 Tint) then
		return $ B ((valueToInt v1) < (valueToInt v2))
	else
		fail $ typeMissmatch v1 v2 Tint

evalExpr (Elte e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType v1 v2 Tint) then
		return $ B ((valueToInt v1) <= (valueToInt v2))
	else
		fail $ typeMissmatch v1 v2 Tint

evalExpr (Eadd e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType v1 v2 Tint) then
		return $ I ((valueToInt v1) + (valueToInt v2))
	else
		fail $ typeMissmatch v1 v2 Tint

evalExpr (Esub e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType v1 v2 Tint) then
		return $ I ((valueToInt v1) - (valueToInt v2))
	else
		fail $ typeMissmatch v1 v2 Tint

evalExpr (Emul e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (checkType v1 v2 Tint) then
		return $ I ((valueToInt v1) * (valueToInt v2))
	else
		fail $ typeMissmatch v1 v2 Tint

evalExpr (Ediv e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (valueToInt v2) == 0 then
		fail $ (show e2) ++ "is equal 0. Can not divide\n"
	else ( if (checkType v1 v2 Tint) then
		return $ I ((valueToInt v1) `div` (valueToInt v2))
	else
		fail $ typeMissmatch v1 v2 Tint)

evalExpr (Eneg e) = do
	v <- evalExpr e
	if ((toType v) == Tbool) then
		return $ B (not (valueToBool v))
	else
		fail $ typeMissmatchS v Tbool

evalExpr (Emin e) = do
	v <- evalExpr e
	if ((toType v) == Tint) then
		return $ I (-(valueToInt v))
	else
		fail $ typeMissmatchS v Tint


--  | Earr Exp Exp
--  | Efn LIdent
--  | Efnp LIdent [Exp]
--  | Evar [LIdent]

evalExpr (Econ c) = do
	case c of
		Efalse -> return $ B False
		Etrue -> return $ B True
		Eint i -> return $ I i
