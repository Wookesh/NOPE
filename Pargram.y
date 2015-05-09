-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module Pargram where
import Absgram
import Lexgram
import ErrM

}

%name pProgram Program

-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype { Token }

%token 
 '!' { PT _ (TS _ 1) }
 '!=' { PT _ (TS _ 2) }
 '&&' { PT _ (TS _ 3) }
 '(' { PT _ (TS _ 4) }
 ')' { PT _ (TS _ 5) }
 '*' { PT _ (TS _ 6) }
 '+' { PT _ (TS _ 7) }
 ',' { PT _ (TS _ 8) }
 '-' { PT _ (TS _ 9) }
 '.' { PT _ (TS _ 10) }
 '/' { PT _ (TS _ 11) }
 ':' { PT _ (TS _ 12) }
 ';' { PT _ (TS _ 13) }
 '<' { PT _ (TS _ 14) }
 '<=' { PT _ (TS _ 15) }
 '=' { PT _ (TS _ 16) }
 '==' { PT _ (TS _ 17) }
 '>' { PT _ (TS _ 18) }
 '>=' { PT _ (TS _ 19) }
 'Array' { PT _ (TS _ 20) }
 'Bool' { PT _ (TS _ 21) }
 'DEDENT' { PT _ (TS _ 22) }
 'INDENT' { PT _ (TS _ 23) }
 'Int' { PT _ (TS _ 24) }
 'NEWLINE' { PT _ (TS _ 25) }
 'NEWLINE else' { PT _ (TS _ 26) }
 '[' { PT _ (TS _ 27) }
 ']' { PT _ (TS _ 28) }
 'def' { PT _ (TS _ 29) }
 'do' { PT _ (TS _ 30) }
 'false' { PT _ (TS _ 31) }
 'for' { PT _ (TS _ 32) }
 'func' { PT _ (TS _ 33) }
 'if' { PT _ (TS _ 34) }
 'in' { PT _ (TS _ 35) }
 'return' { PT _ (TS _ 36) }
 'then' { PT _ (TS _ 37) }
 'true' { PT _ (TS _ 38) }
 'while' { PT _ (TS _ 39) }
 '||' { PT _ (TS _ 40) }

L_integ  { PT _ (TI $$) }
L_RecName { PT _ (T_RecName $$) }
L_LIdent { PT _ (T_LIdent $$) }
L_err    { _ }


%%

Integer :: { Integer } : L_integ  { (read ( $1)) :: Integer }
RecName    :: { RecName} : L_RecName { RecName ($1)}
LIdent    :: { LIdent} : L_LIdent { LIdent ($1)}

Program :: { Program }
Program : ListDecl { Prog $1 } 


Decl :: { Decl }
Decl : 'func' Type LIdent '(' ListPDecl ')' StmtB { Dfun $2 $3 $5 $7 } 
  | 'func' LIdent '(' ListPDecl ')' StmtB { Dproc $2 $4 $6 }
  | 'def' RecName 'NEWLINE' 'INDENT' ListVDecl 'DEDENT' { Drec $2 $5 }
  | StmtLine { Dstmt $1 }


ListDecl :: { [Decl] }
ListDecl : Decl { (:[]) $1 } 
  | Decl 'NEWLINE' ListDecl { (:) $1 $3 }


StmtLine :: { StmtLine }
StmtLine : StmtL { Sline $1 } 


StmtB :: { StmtB }
StmtB : 'NEWLINE' 'INDENT' ListStmtL 'DEDENT' { Sblock $3 } 


StmtL :: { StmtL }
StmtL : ListStmt { Slst $1 } 


ListStmtL :: { [StmtL] }
ListStmtL : StmtL { (:[]) $1 } 
  | StmtL 'NEWLINE' ListStmtL { (:) $1 $3 }


Stmt :: { Stmt }
Stmt : 'if' Exp 'then' StmtB { Sif $2 $4 } 
  | 'if' Exp 'then' StmtB 'NEWLINE else' StmtB { Sife $2 $4 $6 }
  | 'while' Exp 'do' StmtB { Swh $2 $4 }
  | 'for' LIdent 'in' Exp 'do' StmtB { Sfor $2 $4 $6 }
  | 'return' Exp { Sret $2 }
  | Exp { Sfcll $1 }
  | LIdent '=' Exp { Sass $1 $3 }
  | SDecl { Sdecl $1 }


ListStmt :: { [Stmt] }
ListStmt : Stmt { (:[]) $1 } 
  | Stmt ';' ListStmt { (:) $1 $3 }


SDecl :: { SDecl }
SDecl : VDecl { Svar $1 } 
  | VDecl '=' Exp { Svas $1 $3 }


VDecl :: { VDecl }
VDecl : Type LIdent { VDcl $1 $2 } 


PDecl :: { PDecl }
PDecl : VDecl { PDcl $1 } 


ListPDecl :: { [PDecl] }
ListPDecl : {- empty -} { [] } 
  | PDecl { (:[]) $1 }
  | PDecl ',' ListPDecl { (:) $1 $3 }


ListVDecl :: { [VDecl] }
ListVDecl : VDecl { (:[]) $1 } 
  | VDecl 'NEWLINE' ListVDecl { (:) $1 $3 }


Exp :: { Exp }
Exp : '[' Exp ':' Exp ']' { EdarR $2 $4 } 
  | '[' ListExp ']' { Edarr $2 }
  | Exp2 { $1 }


Exp2 :: { Exp }
Exp2 : Exp2 '||' Exp3 { Eor $1 $3 } 
  | Exp3 { $1 }


Exp3 :: { Exp }
Exp3 : Exp3 '&&' Exp4 { Eand $1 $3 } 
  | Exp4 { $1 }


Exp4 :: { Exp }
Exp4 : Exp4 '==' Exp5 { Eeq $1 $3 } 
  | Exp4 '!=' Exp5 { Edif $1 $3 }
  | Exp5 { $1 }


Exp5 :: { Exp }
Exp5 : Exp5 '>' Exp6 { Egt $1 $3 } 
  | Exp5 '>=' Exp6 { Egte $1 $3 }
  | Exp5 '<' Exp6 { Elt $1 $3 }
  | Exp5 '<=' Exp6 { Elte $1 $3 }
  | Exp6 { $1 }


Exp6 :: { Exp }
Exp6 : Exp6 '+' Exp7 { Eadd $1 $3 } 
  | Exp6 '-' Exp7 { Esub $1 $3 }
  | Exp7 { $1 }


Exp7 :: { Exp }
Exp7 : Exp7 '*' Exp8 { Emul $1 $3 } 
  | Exp7 '/' Exp8 { Ediv $1 $3 }
  | Exp8 { $1 }


Exp8 :: { Exp }
Exp8 : '!' Exp9 { Eneg $2 } 
  | '-' Exp9 { Emin $2 }
  | Exp9 { $1 }


Exp9 :: { Exp }
Exp9 : Exp9 '[' Exp ']' { Earr $1 $3 } 
  | LIdent '(' ')' { Efn $1 }
  | LIdent '(' ListExp ')' { Efnp $1 $3 }
  | Exp10 { $1 }


Exp10 :: { Exp }
Exp10 : ListLIdent { Evar $1 } 
  | Constant { Econ $1 }
  | '(' Exp ')' { $2 }


Constant :: { Constant }
Constant : 'false' { Efalse } 
  | 'true' { Etrue }
  | Integer { Eint $1 }


Type :: { Type }
Type : 'Int' { Tint } 
  | 'Bool' { Tbool }
  | RecName { Trec $1 }
  | 'Array' Type { Tarr $2 }


ListExp :: { [Exp] }
ListExp : Exp { (:[]) $1 } 
  | Exp ',' ListExp { (:) $1 $3 }


ListLIdent :: { [LIdent] }
ListLIdent : LIdent { (:[]) $1 } 
  | LIdent '.' ListLIdent { (:) $1 $3 }



{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
}

