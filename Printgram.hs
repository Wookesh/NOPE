{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Printgram where

-- pretty-printer generated by the BNF converter

import Absgram
import Data.Char


-- the top-level printing method
printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : "," :ts -> showString t . space "," . rend i ts
    t  : ")" :ts -> showString t . showChar ')' . rend i ts
    t  : "]" :ts -> showString t . showChar ']' . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else (' ':s))

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- the printer class does the job
class Print a where
  prt :: Int -> a -> Doc
  prtList :: [a] -> Doc
  prtList = concatD . map (prt 0)

instance Print a => Print [a] where
  prt _ = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j<i then parenth else id


instance Print Integer where
  prt _ x = doc (shows x)


instance Print Double where
  prt _ x = doc (shows x)



instance Print RecName where
  prt _ (RecName i) = doc (showString ( i))


instance Print LIdent where
  prt _ (LIdent i) = doc (showString ( i))
  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ".") , prt 0 xs])



instance Print Program where
  prt i e = case e of
   Prog decls -> prPrec i 0 (concatD [prt 0 decls])


instance Print Decl where
  prt i e = case e of
   Dfun type' lident pdecls stmtb -> prPrec i 0 (concatD [doc (showString "func") , prt 0 type' , prt 0 lident , doc (showString "(") , prt 0 pdecls , doc (showString ")") , doc (showString "NEWLINE") , prt 0 stmtb])
   Dproc lident pdecls stmtb -> prPrec i 0 (concatD [doc (showString "func") , prt 0 lident , doc (showString "(") , prt 0 pdecls , doc (showString ")") , doc (showString "NEWLINE") , prt 0 stmtb])
   Drec recname vdecls -> prPrec i 0 (concatD [doc (showString "def") , prt 0 recname , doc (showString "NEWLINE") , doc (showString "INDENT") , prt 0 vdecls , doc (showString "DEDENT")])
   Dstmt stmtline -> prPrec i 0 (concatD [prt 0 stmtline])

  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString "NEWLINE") , prt 0 xs])

instance Print StmtLine where
  prt i e = case e of
   Sline stmtl -> prPrec i 0 (concatD [prt 0 stmtl])


instance Print StmtB where
  prt i e = case e of
   Sblock stmtls -> prPrec i 0 (concatD [doc (showString "INDENT") , prt 0 stmtls , doc (showString "DEDENT")])


instance Print StmtL where
  prt i e = case e of
   Slst stmts -> prPrec i 0 (concatD [prt 0 stmts])

  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString "NEWLINE") , prt 0 xs])

instance Print Stmt where
  prt i e = case e of
   Sif exp stmtb -> prPrec i 0 (concatD [doc (showString "if") , prt 0 exp , doc (showString "then") , prt 0 stmtb])
   Sife exp stmtb0 stmtb -> prPrec i 0 (concatD [doc (showString "if") , prt 0 exp , doc (showString "then") , prt 0 stmtb0 , doc (showString "else") , prt 0 stmtb])
   Swh exp stmtb -> prPrec i 0 (concatD [doc (showString "while") , prt 0 exp , doc (showString "do") , prt 0 stmtb])
   Sfor lident exp stmtb -> prPrec i 0 (concatD [doc (showString "for") , prt 0 lident , doc (showString "in") , prt 0 exp , doc (showString "do") , prt 0 stmtb])
   Sret exp -> prPrec i 0 (concatD [doc (showString "return") , prt 0 exp])
   Sfcll exp -> prPrec i 0 (concatD [prt 0 exp])
   Sass lident exp -> prPrec i 0 (concatD [prt 0 lident , doc (showString "=") , prt 0 exp])
   Sdecl sdecl -> prPrec i 0 (concatD [prt 0 sdecl])

  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print SDecl where
  prt i e = case e of
   Svar vdecl -> prPrec i 0 (concatD [prt 0 vdecl])
   Svas vdecl exp -> prPrec i 0 (concatD [prt 0 vdecl , doc (showString "=") , prt 0 exp])


instance Print VDecl where
  prt i e = case e of
   VDcl type' lident -> prPrec i 0 (concatD [prt 0 type' , prt 0 lident])

  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString "NEWLINE") , prt 0 xs])

instance Print PDecl where
  prt i e = case e of
   PDcl vdecl -> prPrec i 0 (concatD [prt 0 vdecl])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print Exp where
  prt i e = case e of
   Edarr exps -> prPrec i 0 (concatD [doc (showString "[") , prt 0 exps , doc (showString "]")])
   Eor exp0 exp -> prPrec i 2 (concatD [prt 2 exp0 , doc (showString "||") , prt 3 exp])
   Eand exp0 exp -> prPrec i 3 (concatD [prt 3 exp0 , doc (showString "&&") , prt 4 exp])
   Eeq exp0 exp -> prPrec i 4 (concatD [prt 4 exp0 , doc (showString "==") , prt 5 exp])
   Edif exp0 exp -> prPrec i 4 (concatD [prt 4 exp0 , doc (showString "!=") , prt 5 exp])
   Egt exp0 exp -> prPrec i 5 (concatD [prt 5 exp0 , doc (showString ">") , prt 6 exp])
   Egte exp0 exp -> prPrec i 5 (concatD [prt 5 exp0 , doc (showString ">=") , prt 6 exp])
   Elt exp0 exp -> prPrec i 5 (concatD [prt 5 exp0 , doc (showString "<") , prt 6 exp])
   Elte exp0 exp -> prPrec i 5 (concatD [prt 5 exp0 , doc (showString "<=") , prt 6 exp])
   Eadd exp0 exp -> prPrec i 6 (concatD [prt 6 exp0 , doc (showString "+") , prt 7 exp])
   Esub exp0 exp -> prPrec i 6 (concatD [prt 6 exp0 , doc (showString "-") , prt 7 exp])
   Emul exp0 exp -> prPrec i 7 (concatD [prt 7 exp0 , doc (showString "*") , prt 8 exp])
   Ediv exp0 exp -> prPrec i 7 (concatD [prt 7 exp0 , doc (showString "/") , prt 8 exp])
   Eneg exp -> prPrec i 8 (concatD [doc (showString "!") , prt 9 exp])
   Emin exp -> prPrec i 8 (concatD [doc (showString "-") , prt 9 exp])
   Earr exp0 exp -> prPrec i 9 (concatD [prt 9 exp0 , doc (showString "[") , prt 0 exp , doc (showString "]")])
   Efn lident -> prPrec i 9 (concatD [prt 0 lident , doc (showString "(") , doc (showString ")")])
   Efnp lident exps -> prPrec i 9 (concatD [prt 0 lident , doc (showString "(") , prt 0 exps , doc (showString ")")])
   Evar lidents -> prPrec i 10 (concatD [prt 0 lidents])
   Econ constant -> prPrec i 10 (concatD [prt 0 constant])

  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print Constant where
  prt i e = case e of
   Efalse  -> prPrec i 0 (concatD [doc (showString "false")])
   Etrue  -> prPrec i 0 (concatD [doc (showString "true")])
   Eint n -> prPrec i 0 (concatD [prt 0 n])


instance Print Type where
  prt i e = case e of
   Tint  -> prPrec i 0 (concatD [doc (showString "Int")])
   Tbool  -> prPrec i 0 (concatD [doc (showString "Bool")])
   Trec recname -> prPrec i 0 (concatD [prt 0 recname])
   Tarr type' -> prPrec i 0 (concatD [doc (showString "Array") , prt 0 type'])



