module Evalgram where

import Absgram
import Data.Map as M
import Control.Monad.State
import Data.Maybe

-- data Variable = TInt Int | TBool Bool | TArr Type [Variable] | TRec [Variable]

-- data Type = TInt | TBool | TArr Type | TRec

-- data Val = Int | Bool deriving (Eq,Ord,Show)

type Val = Int

type Loc = Int 

data Obj = Fun StmtB | Var Loc deriving (Eq,Ord,Show)

type Env = M.Map LIdent Obj 

type Store = (M.Map Loc (Type, Val), Loc)

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

alloc typ = do
	PS (e, (m, loc)) <- get
	put $ PS (e, (M.insert (loc + 1) (typ, 0) m, loc + 1))
	return $ loc + 1


evalProgram p = evalState (evalProg p) initialState

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
-- 
evalStmt (Sdecl sDecl) = do
	evalSDecl sDecl

evalSDecl (Svar vDecl) = do
	evalVDecl vDecl

evalVDecl (VDcl typ lident) = do
	loc <- alloc typ
	addVar lident loc
