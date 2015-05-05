module Evalgram where

import Absgram
import Data.Map as M
import Control.Monad.State
import Data.Maybe

data Value = I Integer | B Bool | Ar Type [Value] | Rc RecName [(Type, Value)] | None deriving (Eq,Ord,Show)

type Loc = Int 

data Obj = Fun Type [Type] StmtB | Var Loc deriving (Eq,Ord,Show)

type Env = M.Map LIdent Obj 

type Store = (M.Map Loc (Type, Value), Loc)

type TypeMap = M.Map LIdent Type
type FTypeMap = M.Map LIdent (Type, [Type])

data PState = PS (Env, Store) deriving (Eq,Ord,Show)
data TStore = TS (FTypeMap, TypeMap) deriving (Eq,Ord,Show)

clearEnv :: Env
clearEnv = M.empty

clearStore :: Store
clearStore = (M.empty, 0)

clearTMap :: TypeMap
clearTMap = M.empty

clearFTMap :: FTypeMap
clearFTMap = M.empty

initialState :: PState
initialState = PS (clearEnv, clearStore)

initialTState :: TStore
initialTState = TS (clearFTMap, clearTMap)

-------------------------------------
-- Environment and Store functions --
-------------------------------------

addVar lident loc = do
	PS (env, s) <- get
	put $ PS (M.insert lident (Var loc) env, s)

getLoc lident = do
	PS (env, s) <- get
	case M.lookup lident env of
		Just (Fun _ _ _) -> fail "Expectec variable, not function name"
		Just (Var l) -> return $ l
		Nothing -> fail $ "Undefined variable" ++ (show lident) ++ ".\n"

getVal lident = do
	loc <- getLoc lident
	PS (_, (store, _)) <- get
	case M.lookup loc store of 
		(Just val) -> return val
		Nothing -> fail "Location unalloced"

alloc typ = do
	PS (e, (m, loc)) <- get
	put $ PS (e, (M.insert (loc + 1) (typ, defaultValue typ) m, loc + 1))
	return $ loc + 1

assign val loc = do
	PS (e, (store, l)) <- get
	case M.lookup loc store of
		Just (typ, _) -> if (typeMatches typ val) then
				put $ PS (e, (M.insert loc (typ, val) store, l))
			else
				fail $ "Expected " ++ (show typ) ++ ", got " ++ (show (toType val)) ++ ".\n"
		Nothing -> fail "Location unalloced"


allocType typ lident = do
	TS (e, store) <- get
	put $ TS (e, M.insert lident typ store)

getVarType lident = do
	TS (_, store) <- get
	case M.lookup lident store of
		(Just typ) -> return typ
		Nothing -> fail "Location unalloced"

registerFunc typ pTypes lident = do
	TS (fstore, s) <- get
	put $ TS (M.insert lident (typ, pTypes) fstore, s)

getFunType lident = do
	TS (fstore, _) <- get
	case M.lookup lident fstore of
		(Just (typ, _)) -> return typ
		Nothing -> fail "Location unalloced"

getFunParamsTypes lident = do
	TS (fstore, _) <- get
	case M.lookup lident fstore of
		(Just (_, types)) -> return types
		Nothing -> fail "Location unalloced"
------------------
-- Type Control --
------------------

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

checkType e1 e2 type_ = (toType e1) == type_ && (toType e2) == type_ 
checkType_ e1 e2 = (toType e1) == (toType e2)

typeMissmatch t1 t2 type_ = "Could not match type (" ++ (show t1) ++ ") or (" ++ (show t2) ++ ") with type " ++ (show type_) ++ ".\n"
typeMissmatch_ t1 t2 = "Could not match type (" ++ (show t1) ++ ") and (" ++ (show t2) ++ ").\n"
typeMissmatchS t typ = "Could not match type (" ++ (show t) ++ ") with " ++ (show typ) ++ ".\n"


-------------
-- Program --
-------------

evalProgram p = runState (evalProg p) initialState

checkProgram p = return $ runState (checkProg p) initialTState

evalProg (Prog decls) = do
	val <- foldM evalDecl None decls
	return val


checkProg (Prog decls) = do
	val <- foldM checkDecl Tvoid decls
	return $ val == Tint || val == Tvoid

------------------
-- Declarations --
------------------

evalDecl val (Dstmt stmtL) = do
	val <- evalStmtLine val stmtL
	return val



checkDecl val (Dstmt stmtL) = do
	val <- checkStmtLine val stmtL
	return val

checkDecl val (Dfun typ lIdent pDecls stmtB) = do
	pTypes <- foldM (\l s -> return $ l ++ (checkPDecl s)) [] pDecls
	registerFunc typ pTypes lIdent
	val <- checkStmtB Tvoid stmtB
	if val == typ then
		return Tvoid
	else
		fail $ typeMissmatchS val typ

checkDecl val (Dproc lIdent pDecls stmtB) = do
	pTypes <- foldM (\l s -> return $ l ++ (checkPDecl s)) [] pDecls
	registerFunc Tvoid pTypes lIdent
	val <- checkStmtB Tvoid stmtB
	return val

-- checkDecl val (Drec recName vDecls) = do
-- 	return Tvoid


----------------------------
-- Parameter Declarations --
----------------------------

checkPDecl (PDcl vDecl) = do
	t <- checkVDeclF vDecl
	return t


---------------------------------
-- Statements Blocks and Lists --
---------------------------------

-- Eval

evalStmtLine val (Sline stmtL) = do
	val <- evalStmtL val stmtL
	return val

evalStmtB val (Sblock stmtL) = do
	val <- foldM evalStmtL val stmtL
	return val

evalStmtL val (Slst stmts) = do
	val <- foldM evalStmt val stmts
	return val

-- Check Types

checkStmtLine val (Sline stmtL) = do
	val <- checkStmtL val stmtL
	return val

checkStmtB val (Sblock stmtL) = do
	val <- foldM checkStmtL val stmtL
	return val

checkStmtL val (Slst stmts) = do
	val <- foldM checkStmt val stmts
	return val

----------------
-- Statements --
----------------

-- if expr then stmt
evalStmt None (Sif expr stmtB) = do
	v <- evalExpr expr
	if ((toType v) == Tbool) then
		if (valueToBool v) then do
			val <- evalStmtB None stmtB
			return val 
		else 
			return None
	else
		fail $ typeMissmatchS v Tbool

-- if expr then stmt else stmt
evalStmt None (Sife expr stmtB1 stmtB2) = do
	v <- evalExpr expr
	if ((toType v) == Tbool) then
		if (valueToBool v) then do
			val <- evalStmtB None stmtB1
			return val 
		else do
			val <- evalStmtB None stmtB2
			return val 
	else
		fail $ typeMissmatchS v Tbool

-- while expr stmt
evalStmt None stmt@(Swh expr stmtB) = do
	v <- evalExpr expr
	if ((toType v) == Tbool) then
		if (valueToBool v) then do
			val <- evalStmtB None stmtB
			val <- evalStmt val stmt
			return val 
		else 
			return None
	else
		fail $ typeMissmatchS v Tbool

--  | Sfor LIdent Exp StmtB

-- return expr
evalStmt None (Sret expr) = do
	v <- evalExpr expr
	return v

-- function call or expression without direct effect
evalStmt None (Sfcll expr) = do
	val <- evalExpr expr
	return None

-- var = expr
evalStmt None (Sass lident expr) = do
	v <- evalExpr expr
	loc <- getLoc lident
	assign v loc
	return None

-- Type var
evalStmt None (Sdecl sDecl) = do
	evalSDecl sDecl
	return None

-- passing non None value
evalStmt val _ = return val


-- check types in statements

checkStmt Tvoid (Sif expr stmtB) = do
	t <- checkExpr expr
	if (t == Tbool) then do
		val <- checkStmtB Tvoid stmtB
		return val
	else
		fail $ typeMissmatchS t Tbool

checkStmt Tvoid (Sife expr stmtB1 stmtB2) = do
	t <- checkExpr expr
	if (t == Tbool) then do
		val <- checkStmtB Tvoid stmtB1
		val <- checkStmtB val stmtB2
		return val 
	else
		fail $ typeMissmatchS t Tbool

checkStmt Tvoid (Swh expr stmtB) = do
	t <- checkExpr expr
	if (t == Tbool) then do
		val <- checkStmtB Tvoid stmtB
		return val
	else
		fail $ typeMissmatchS t Tbool

--  | Sfor LIdent Exp StmtB
checkStmt Tvoid (Sfor lident expr stmtB) = do
	-- TODO check ident
	t <- checkExpr expr
	val <- checkStmtB Tvoid stmtB
	return Tvoid

checkStmt Tvoid (Sret expr) = do
	t <- checkExpr expr
	return t

checkStmt Tvoid (Sfcll expr) = do
	t <- checkExpr expr
	return Tvoid

checkStmt Tvoid (Sass lident expr) = do
	t <- checkExpr expr
	locType <- getVarType lident
	if t == locType then 
		return Tvoid
	else
		fail $ typeMissmatchS t locType

checkStmt Tvoid (Sdecl sDecl) = do
	val <- checkSDecl sDecl
	return val

checkStmt val _ = return val

---------------------------
-- Variable Declarations --
---------------------------

evalSDecl (Svar vDecl) = do
	loc <- evalVDecl vDecl
	return None

evalSDecl (Svas vDecl expr) = do
	loc <- evalVDecl vDecl
	val <- evalExpr expr
	assign val loc
	return None

evalVDecl (VDcl typ lident) = do
	loc <- alloc typ
	addVar lident loc
	return loc



checkSDecl (Svar vDecl) = do
	checkVDecl vDecl
	return Tvoid

checkSDecl (Svas vDecl expr) = do
	t <- checkExpr expr
	lident <- checkVDecl vDecl
	locType <- getVarType lident
	if t == locType then
		return Tvoid
	else
		fail $ typeMissmatchS t locType

checkVDecl (VDcl typ lident) = do
	allocType typ lident
	return lident

checkVDeclF (VDcl typ lident) = do
	return typ

-----------------
-- Expressions --
-----------------

-- evalExpr (Edarr exprs) = do
-- 	array <- foldr  exprs

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

evalExpr (Evar (i:is)) = do
	ret <- getVal i
	case ret of
		(Tint, val) -> if (is == []) then (return val) else fail $ "Variable " ++ (show i) ++ " is not a Record type"
		(Tbool, val) -> if (is == []) then (return val) else fail $ "Variable " ++ (show i) ++ " is not a Record type"
		(Tarr typ, val) -> if (is == []) then (return val) else fail $ "Variable " ++ (show i) ++ " is not a Record type"
-- 		(Trec, val) -> if (is == []) then (return val) else fail $ "Variable " ++ (show i) ++ " is not a Record type"

evalExpr (Econ c) = do
	case c of
		Efalse -> return $ B False
		Etrue -> return $ B True
		Eint i -> return $ I i


-- Check Expresion Type

checkExpr (Eor e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tbool && t2 == Tbool) then
		return Tbool
	else
		fail $ typeMissmatch t1 t2 Tbool

checkExpr (Eand e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tbool && t2 == Tbool) then
		return Tbool
	else
		fail $ typeMissmatch t1 t2 Tbool

checkExpr (Eeq e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tint && t2 == Tint) then
		return Tbool
	else
		fail $ typeMissmatch t1 t2 Tint

checkExpr (Edif e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tint && t2 == Tint) then
		return Tbool
	else
		fail $ typeMissmatch t1 t2 Tint

checkExpr (Egt e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tint && t2 == Tint) then
		return Tbool
	else
		fail $ typeMissmatch t1 t2 Tint

checkExpr (Egte e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tint && t2 == Tint) then
		return Tbool
	else
		fail $ typeMissmatch t1 t2 Tint

checkExpr (Elt e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tint && t2 == Tint) then
		return Tbool
	else
		fail $ typeMissmatch t1 t2 Tint

checkExpr (Elte e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tint && t2 == Tint) then
		return Tbool
	else
		fail $ typeMissmatch t1 t2 Tint

checkExpr (Eadd e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tint && t2 == Tint) then
		return Tint
	else
		fail $ typeMissmatch t1 t2 Tint

checkExpr (Esub e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tint && t2 == Tint) then
		return Tint
	else
		fail $ typeMissmatch t1 t2 Tint

checkExpr (Emul e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tint && t2 == Tint) then
		return Tint
	else
		fail $ typeMissmatch t1 t2 Tint

checkExpr (Ediv e1 e2) = do
	t1 <- checkExpr e1
	t2 <- checkExpr e2
	if (t1 == Tint && t2 == Tint) then
		return Tint
	else
		fail $ typeMissmatch t1 t2 Tint

checkExpr (Eneg e) = do
	t <- checkExpr e
	if (t == Tbool) then
		return Tbool
	else
		fail $ typeMissmatchS t Tbool

checkExpr (Emin e) = do
	t <- checkExpr e
	if (t == Tint) then
		return Tint
	else
		fail $ typeMissmatchS t Tint

--  | Earr Exp Exp
checkExpr (Efn lIdent) = do
	t <- getFunType lIdent
	return t

--  | Efnp LIdent [Exp]

checkExpr (Evar (i:is)) = do
	typ <- getVarType i
	case typ of
		(Tint) -> if (is == []) then (return Tint) else fail $ "Variable " ++ (show i) ++ " is not a Record type"
		(Tbool) -> if (is == []) then (return Tbool) else fail $ "Variable " ++ (show i) ++ " is not a Record type"
		(Tarr typ1) -> if (is == []) then (return $ Tarr typ) else fail $ "Variable " ++ (show i) ++ " is not a Record type"
-- 		(Trec, val) -> if (is == []) then (return val) else fail $ "Variable " ++ (show i) ++ " is not a Record type"

checkExpr (Econ c) = do
	case c of
		Efalse -> return $ Tbool
		Etrue -> return $ Tbool
		Eint i -> return $ Tint
