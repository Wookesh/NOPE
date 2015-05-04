module Absgram where

-- Haskell module generated by the BNF converter


newtype RecName = RecName String deriving (Eq,Ord,Show)
newtype LIdent = LIdent String deriving (Eq,Ord,Show)
data Program =
   Prog [Decl]
  deriving (Eq,Ord,Show)

data Decl =
   Dfun Type LIdent [PDecl] StmtB
 | Dproc LIdent [PDecl] StmtB
 | Drec RecName [VDecl]
 | Dstmt StmtLine
  deriving (Eq,Ord,Show)

data StmtLine =
   Sline StmtL
  deriving (Eq,Ord,Show)

data StmtB =
   Sblock [StmtL]
  deriving (Eq,Ord,Show)

data StmtL =
   Slst [Stmt]
  deriving (Eq,Ord,Show)

data Stmt =
   Sif Exp StmtB
 | Sife Exp StmtB StmtB
 | Swh Exp StmtB
 | Sfor LIdent Exp StmtB
 | Sret Exp
 | Sfcll Exp
 | Sass LIdent Exp
 | Sdecl SDecl
  deriving (Eq,Ord,Show)

data SDecl =
   Svar VDecl
 | Svas VDecl Exp
  deriving (Eq,Ord,Show)

data VDecl =
   VDcl Type LIdent
  deriving (Eq,Ord,Show)

data PDecl =
   PDcl VDecl
  deriving (Eq,Ord,Show)

data Exp =
   Edarr [Exp]
 | Eor Exp Exp
 | Eand Exp Exp
 | Eeq Exp Exp
 | Edif Exp Exp
 | Egt Exp Exp
 | Egte Exp Exp
 | Elt Exp Exp
 | Elte Exp Exp
 | Eadd Exp Exp
 | Esub Exp Exp
 | Emul Exp Exp
 | Ediv Exp Exp
 | Eneg Exp
 | Emin Exp
 | Earr Exp Exp
 | Efn LIdent
 | Efnp LIdent [Exp]
 | Evar [LIdent]
 | Econ Constant
  deriving (Eq,Ord,Show)

data Constant =
   Efalse
 | Etrue
 | Eint Integer
  deriving (Eq,Ord,Show)

data Type =
   Tint
 | Tbool
 | Trec RecName
 | Tarr Type
  deriving (Eq,Ord,Show)

