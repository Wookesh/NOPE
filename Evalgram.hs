module Evalgram where

import Absgram
import Data.Map as M
import Control.Monad.State
import Data.Maybe

data Value = I Integer | B Bool | Ar Type [Value] | Rc RecName [M.Map LIdent Loc] | None deriving (Eq,Ord,Show)

type Loc = Int 

data Obj = Fun Type [Type] StmtB | Var Loc deriving (Eq,Ord,Show)

type Env = M.Map LIdent Obj 

type VEnv = M.Map LIdent Loc
type FEnv = M.Map LIdent ([PDecl], StmtB)

type Store = (M.Map Loc (Type, Value), Loc)

type TypeMap = M.Map LIdent Type
type FTypeMap = M.Map LIdent (Type, [(Type, LIdent)])

data PState = PS (Env, Store) deriving (Eq,Ord,Show)
data NStore = NS (FEnv, VEnv, Store) deriving (Eq, Ord, Show)
data TStore = TS (FTypeMap, TypeMap) deriving (Eq,Ord,Show)

clearEnv :: Env
clearEnv = M.empty

clearFEnv :: FEnv
clearFEnv = M.empty

clearVEnv :: VEnv
clearVEnv = M.empty

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

initialNStore :: NStore
initialNStore = NS (clearFEnv, clearVEnv, clearStore)

-------------------------------------
-- Environment and Store functions --
-------------------------------------

addVar lident loc = do
	NS (f, venv, s) <- get
	put $ NS (f, M.insert lident loc venv, s)

addFun lident typ params stmt = do
	NS (fenv, v, s) <- get
	put $ NS (M.insert lident (params, stmt) fenv, v, s)

getLoc lident = do
	NS (f, venv, s) <- get
	case M.lookup lident venv of
		Just l -> return $ l
		Nothing -> fail $ "Undefined variable" ++ (show lident) ++ ".\n"

getVal lident = do
	loc <- getLoc lident
	NS (_, _, (store, _)) <- get
	case M.lookup loc store of 
		(Just val) -> return val
		Nothing -> fail "Location unalloced."

getFun lident = do
	NS (fenv, _, _) <- get
	case M.lookup lident fenv of
		Just f -> return f
		Nothing -> fail $ "Undefined function" ++ (show lident) ++ ".\n"

alloc typ = do
	NS (f, v, (m, loc)) <- get
	put $ NS (f, v, (M.insert (loc + 1) (typ, defaultValue typ) m, loc + 1))
	return $ loc + 1

assign val loc = do
	NS (f, v, (store, l)) <- get
	case M.lookup loc store of
		Just (typ, _) -> if (typeMatches typ val) then
				put $ NS (f, v, (M.insert loc (typ, val) store, l))
			else
				fail $ "Expected " ++ (show typ) ++ ", got " ++ (show (toType val)) ++ ".\n"
		Nothing -> fail "Location unalloced"


local fun = do
	NS (fenv, venv, store) <- get
	t <- fun
	NS (_, _, store') <- get
	put $ NS (fenv, venv, store')
	return t

localClearVEnv fun  = do
	NS (fenv, venv, store) <- get
	put $ NS (fenv, clearVEnv, store)
	t <- fun
	NS (_, _, store') <- get
	put $ NS (fenv, venv, store')
	return t

localDecl pDecls values fun = do
	NS (fenv, venv, store) <- get
	let declWithVal = zip pDecls values
	forM declWithVal evalPDeclVal 
	t <- fun
	NS (_, _, store') <- get
	put $ NS (fenv, venv, store')
	return t

-- Type control stores

localT fun = do
	TS (env, store) <- get
	t <- fun
	put $ TS (env, store)
	return t

localTDecl pTypes fun = do
	TS (env, store) <- get
	forM pTypes (\(t, l) -> allocType t l)
	t <- fun
	put $ TS (env, store)
	return t


allocType typ lident = do
	TS (e, store) <- get
	put $ TS (e, M.insert lident typ store)

getVarType lident = do
	TS (_, store) <- get
	case M.lookup lident store of
		(Just typ) -> return typ
		Nothing -> fail $ "Variable " ++ (show lident) ++ " undefined.\n"

registerFunc typ pTypes lident = do
	TS (fstore, s) <- get
	put $ TS (M.insert lident (typ, pTypes) fstore, s)

getFunType lident = do
	TS (fstore, _) <- get
	case M.lookup lident fstore of
		(Just (typ, _)) -> return typ
		Nothing -> fail $ "Function " ++ (show lident) ++ " undefined.\n"

getFunParamsTypes lident = do
	TS (fstore, _) <- get
	case M.lookup lident fstore of
		(Just (_, types)) -> return types
		Nothing -> fail $ "Function " ++ (show lident) ++ " undefined.\n"

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

loseTypeFromExpr typ = do
	case typ of
		Tint -> return Tvoid
		Tbool -> return Tvoid
		(Tarr _) -> return Tvoid
		(Trec _) -> return Tvoid
		_ -> return typ

-------------
-- Program --
-------------

evalProgram p = runState (evalProg p) initialNStore

checkProgram p = return $ runState (checkProg p) initialTState

evalProg (Prog decls) = do
	val <- foldM evalDecl None decls
	case val of
		None -> return 0
		(I i) -> return i


checkProg (Prog decls) = do
	val <- foldM checkDecl Tvoid decls
	return $ val == Tint || val == Tvoid

------------------
-- Declarations --
------------------

evalDecl val (Dstmt stmtL) = do
	val <- evalStmtLine val stmtL
	return val

evalDecl val (Dfun typ lIdent pDecls stmtB) = do
	addFun lIdent typ pDecls stmtB
	return None

evalDecl val (Dproc lIdent pDecls stmtB) = do
	addFun lIdent Tvoid pDecls stmtB
	return None


checkDecl val (Dstmt stmtL) = do
	val <- checkStmtLine val stmtL
	return val

checkDecl val (Dfun typ lIdent pDecls stmtB) = do
	pTypes <- foldM (\l s -> return $ l ++ (checkPDecl s)) [] pDecls
	registerFunc typ pTypes lIdent
	val <- localTDecl pTypes $ checkStmtB Tvoid stmtB
	if val == typ then
		return Tvoid
	else
		fail $ typeMissmatchS val typ

checkDecl val (Dproc lIdent pDecls stmtB) = do
	pTypes <- foldM (\l s -> return $ l ++ (checkPDecl s)) [] pDecls
	registerFunc Tvoid pTypes lIdent
	val <- localTDecl pTypes $ checkStmtB Tvoid stmtB
	if (val == Tvoid) then
		return val
	else
		fail $ "Untyped function " ++ (show lIdent) ++ "returned value.\n"

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
	if (valueToBool v) then do
		val <- evalStmtB None stmtB
		return val 
	else 
		return None

-- if expr then stmt else stmt
evalStmt None (Sife expr stmtB1 stmtB2) = do
	v <- evalExpr expr
	if (valueToBool v) then do
		val <- evalStmtB None stmtB1
		return val 
	else do
		val <- evalStmtB None stmtB2
		return val 

-- while expr stmt
evalStmt None stmt@(Swh expr stmtB) = do
	v <- evalExpr expr
	if (valueToBool v) then do
		val <- evalStmtB None stmtB
		val <- evalStmt val stmt
		return val 
	else 
		return None

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
	t <- loseTypeFromExpr t
	val <- checkStmtB t stmtB
	return val

checkStmt Tvoid (Sret expr) = do
	t <- checkExpr expr
	return t

checkStmt Tvoid (Sfcll expr) = do
	t <- checkExpr expr
	t <- loseTypeFromExpr t
	return t

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


evalPDeclVal (PDcl vDecl, val) = do
	loc <- evalVDecl vDecl
	assign val loc
	return ()


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
	return (typ, lident)

-----------------
-- Expressions --
-----------------

-- evalExpr (Edarr exprs) = do
-- 	array <- foldr  exprs

evalExpr (Eor e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ B ((valueToBool v1) || (valueToBool v2))

evalExpr (Eand e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ B ((valueToBool v1) && (valueToBool v2))

evalExpr (Eeq e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ B (v1 == v2)

evalExpr (Edif e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ B (v1 /= v2)

evalExpr (Egt e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ B ((valueToInt v1) > (valueToInt v2))

evalExpr (Egte e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ B ((valueToInt v1) >= (valueToInt v2))

evalExpr (Elt e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ B ((valueToInt v1) < (valueToInt v2))

evalExpr (Elte e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ B ((valueToInt v1) <= (valueToInt v2))

evalExpr (Eadd e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ I ((valueToInt v1) + (valueToInt v2))

evalExpr (Esub e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ I ((valueToInt v1) - (valueToInt v2))

evalExpr (Emul e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	return $ I ((valueToInt v1) * (valueToInt v2))

evalExpr (Ediv e1 e2) = do
	v1 <- evalExpr e1
	v2 <- evalExpr e2
	if (valueToInt v2) == 0 then
		fail $ (show e2) ++ "is equal 0. Can not divide\n"
	else
		return $ I ((valueToInt v1) `div` (valueToInt v2))

evalExpr (Eneg e) = do
	v <- evalExpr e
	return $ B (not (valueToBool v))

evalExpr (Emin e) = do
	v <- evalExpr e
	return $ I (-(valueToInt v))

--  | Earr Exp Exp

evalExpr (Efn lIdent) = do
	(_, stmtB) <- getFun lIdent
	t <- local $ evalStmtB None stmtB
	return t

evalExpr (Efnp lIdent exprs) = do
	(pDecls, stmtB) <- getFun lIdent
	values <- foldM (\l e -> do { v <- evalExpr e; return $ l ++ [v] }) [] exprs
	t <- localDecl pDecls values (evalStmtB None stmtB)
	return t

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

-- stackExprs l expr = do
-- 	t <- evalExpr expr
-- 	return $ l ++ t

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

checkExpr (Earr expr1 expr2) = do
	t1 <- checkExpr expr1
	t2 <- checkExpr expr2
	if t2 == Tint then
		case t1 of 
			(Tarr typ) -> return typ
			_ -> fail $ "Try to access non array by [] operator."
	else
		fail $ typeMissmatchS t1 Tint

checkExpr (Efn lIdent) = do
	t <- getFunType lIdent
	pFunTypes <- getFunParamsTypes lIdent
	if ((length pFunTypes) /= 0) then
		fail $ "Wrong number of parameters"
	else
		return t

checkExpr (Efnp lIdent exprs) = do
	t <- getFunType lIdent
	pFunTypes <- getFunParamsTypes lIdent
	if length(pFunTypes) /= length(exprs) then
		fail $ "Wrong number of parameters"
	else do 
		let s = zipWith (\a b -> (a, b)) pFunTypes exprs
		val <- foldM checkParameterType Tvoid s
		if val == Tvoid then
			return t
		else
			return val

checkExpr (Evar (i:is)) = do
	typ <- getVarType i
	case typ of
		(Tint) -> if (is == []) then (return Tint) else fail $ "Variable " ++ (show i) ++ " is not a Record type"
		(Tbool) -> if (is == []) then (return Tbool) else fail $ "Variable " ++ (show i) ++ " is not a Record type"
		(Tarr typ1) -> if (is == []) then (return $ Tarr typ1) else fail $ "Variable " ++ (show i) ++ " is not a Record type"
-- 		(Trec, val) -> if (is == []) then (return val) else fail $ "Variable " ++ (show i) ++ " is not a Record type"

checkExpr (Econ c) = do
	case c of
		Efalse -> return $ Tbool
		Etrue -> return $ Tbool
		Eint i -> return $ Tint

checkParameterType Tvoid ((typ, lident), expr) = do
	t <- checkExpr expr
	if typ == t then
		return Tvoid
	else
		fail "Failed types in function parameters"

checkParameterType val _ = return val
