{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances #-}

module PrettyRAML where

import Control.Monad.RWS hiding ((<>))
import Control.Arrow (first)
import Data.List (deleteBy)

import Language.Syntactic hiding (match)
import Language.Syntactic.Constructs.Binding.HigherOrder

import Text.PrettyPrint

import Feldspar.Core.Types
import Feldspar.Core.Frontend
import Feldspar.Core.Constructs
import Feldspar.Core.Interpretation

import Feldspar.Core.Constructs.Array
import Feldspar.Core.Constructs.Binding hiding (showVar)
import Feldspar.Core.Constructs.Bits
import Feldspar.Core.Constructs.Complex
import Feldspar.Core.Constructs.Condition
import Feldspar.Core.Constructs.ConditionM
import Feldspar.Core.Constructs.Conversion
import Feldspar.Core.Constructs.Eq
import Feldspar.Core.Constructs.Error
import Feldspar.Core.Constructs.Floating
import Feldspar.Core.Constructs.Fractional
import Feldspar.Core.Constructs.Integral
import Feldspar.Core.Constructs.Literal
import Feldspar.Core.Constructs.Logic
import Feldspar.Core.Constructs.Loop
import Feldspar.Core.Constructs.Mutable
import Feldspar.Core.Constructs.MutableArray
import Feldspar.Core.Constructs.MutableReference
import Feldspar.Core.Constructs.MutableToPure
import Feldspar.Core.Constructs.Num
import Feldspar.Core.Constructs.Ord
import Feldspar.Core.Constructs.Trace
import Feldspar.Core.Constructs.Tuple

type PrettyM = RWS () [Doc] Integer

freshName :: String -> PrettyM String
freshName prefix = do
    i <- get
    put (i+1)
    return $ prefix ++ show i

class Pretty sub
  where
    prettySym :: ( Project (CLambda Type) dom
                 , Project (Variable :|| Type) dom
                 , Pretty dom)
              => sub sig -> Args (AST (Decor Info dom)) a -> PrettyM Doc

instance (Pretty sub1, Pretty sub2) => Pretty (sub1 :+: sub2)
  where
    prettySym (InjL a) args = prettySym a args
    prettySym (InjR a) args = prettySym a args

instance (Pretty sub) => Pretty (sub :|| pred)
  where
    prettySym (C' s) = prettySym s

instance (Pretty dom) => Pretty (Decor info dom)
  where
    prettySym (Decor _ s) = prettySym s

instance Pretty dom

pretty :: ( Pretty dom
          , Project (Variable :|| Type) dom
          , Project (CLambda Type) dom)
       => ASTF (Decor Info dom) a -> PrettyM Doc
pretty = simpleMatch prettySym

toRAML :: SyntacticFeld a => a -> Doc
toRAML expr = vcat w $+$ a $+$ runtime $+$ text "main = ()"
  where
    (a,w) = evalRWS (go [] $ reifyFeld defaultFeldOpts N32 expr) () 0
    go :: [(VarId,Doc)] -> ASTF (Decor Info FeldDom) a -> PrettyM Doc
    go vars (Sym (Decor info lam) :$ body)
        | Just (SubConstr2 (Lambda v)) <- prjLambda lam
        = go ((v,prettyType $ argType $ infoType info):vars) body
    go vars body = do
        b <- pretty body
        return $  name <+> char ':' <+> typesig <+> text "->" <+> bodytype
               $$ name <> args <+> char '=' <+> b <> semi
              
      where
        name    = text "test"
        typesig | null vars = text "unit"
                | otherwise = parens (hcat $ punctuate comma $ map snd $ reverse vars)
        args | null vars = parens (text "dummy")
             | otherwise = parens (hcat $ punctuate comma $ map (showVar . fst) $ reverse vars)
        bodytype = prettyType (infoType $ getInfo body)

instance Pretty (NUM :|| Type)
  where
    prettySym (C' Add) (a :* b :* Nil) = prettyOp (char '+') a b
    prettySym (C' Sub) (a :* b :* Nil) = prettyOp (char '-') a b
    prettySym (C' Mul) (a :* b :* Nil) = prettyOp (char '*') a b

prettyOp op a b = do a' <- pretty a
                     b' <- pretty b
                     return $ parens $ a' <+> op <+> b'

instance Pretty (Literal :|| Type)
  where
    prettySym (C' (Literal l)) Nil = return $ text (show l)

instance Pretty (Variable :|| Type)
  where
    prettySym (C' (Variable v)) Nil = return $ showVar v

instance Pretty (Array :|| Type)
  where
    prettySym (C' Parallel) (len :* (lam :$ body) :* Nil)
        | Just (SubConstr2 (Lambda v)) <- prjLambda lam
        = do
            let fun = text "parallel" <> text (show v)
            let l   = text "len"
            let fv  = map (first showVar) $ freeVars body
            len' <- pretty len
            b'   <- pretty body
            tell [prettyFun fun
                     ((l,text "nat") : fv)
                     (char 'L' <> parens (prettyType (infoType $ getInfo body)))
                     (text "match" <+> l <+> text "with"
                     $$ match (text "0  ") (text "nil")
                     $$ match (text "n+1") (b' <+> cons <+> fun <+> (parens (hsep $ punctuate comma (char 'n' : map fst fv)))))
                 ]
            return $ parens $ fun <+> parens (hcat $ punctuate comma $ len' : map fst fv)

    prettySym (C' GetLength) (arr :* Nil)
        = do arr' <- pretty arr
             return $ callByType (text "getLength") (elemType $ infoType $ getInfo arr) [arr']

    prettySym (C' GetIx) (arr :* ix :* Nil)
        = do arr' <- pretty arr
             ix'  <- pretty ix
             return $ callByType (text "getIx") (elemType $ infoType $ getInfo arr) [arr',ix']

elemType :: TypeRep a -> Doc
elemType (ArrayType t) = prettyType t

callByType :: Doc -> Doc -> [Doc] -> Doc
callByType prefix t args = prefix <> char '_' <> t <+> (parens (hsep $ punctuate comma args))

instance Pretty (Loop :|| Type)
  where
    prettySym (C' ForLoop) (len :* init :* step@(lam1 :$ (lam2 :$ body)) :* Nil)
        | Just (SubConstr2 (Lambda v1)) <- prjLambda lam1
        , Just (SubConstr2 (Lambda v2)) <- prjLambda lam2
        = do
            let fun = text "forLoop" <> text (show v1)
            let l   = text "len"
                lt  = text "nat"
                i   = showVar v1
                it  = text "nat"
                s   = showVar v2
                st  = text "nat" -- TODO extract the type of the state variable
            let fv  = map (first showVar) $ freeVars step
            len'  <- pretty len
            init' <- pretty init
            b'    <- pretty body
            tell [prettyFun fun
                     ((l,lt) : (i,it) : (s,st) : fv)
                     (prettyType (infoType $ getInfo body))
                     (text "match" <+> l <+> text "with"
                     $$ match (text "0  ") s
                     $$ match (text "n+1") (fun <+> (parens (hsep $ punctuate comma (char 'n' : i <> text "+1" : b' : map fst fv)))))
                 ]
            return $ parens $ fun <+> parens (hcat $ punctuate comma $ len' : char '0' : init' : map fst fv)

cons = colon <> colon

match :: Doc -> Doc -> Doc
match c body = char '|' <+> c <+> text "->" <+> body

-- * Free Variables
--
universe :: ASTF dom a -> [ASTE dom]
universe a = ASTE a : go a
 where
   go :: AST dom a -> [ASTE dom]
   go (Sym s)  = []
   go (s :$ a) = go s ++ universe a

freeVars :: ( Project (Variable :|| Type) dom
            , Project (CLambda Type) dom
            )
         => AST (Decor Info dom) a -> [(VarId,Doc)]
freeVars (Sym (Decor info (prjF -> Just (C' (Variable v))))) = [(v,prettyType $ infoType info)]
freeVars ((prjLambda -> Just (SubConstr2 (Lambda v))) :$ body) = filter ((Prelude./=v).fst) (freeVars body)
freeVars (Sym _)  = []
freeVars (s :$ a) = freeVars s ++ freeVars a

-- * Helper functions
--

prettyFun :: Doc -> [(Doc,Doc)] -> Doc -> Doc -> Doc
prettyFun name vars rtype body =  name <+> colon <+> typesig <+> text "->" <+> rtype
                               $$ name <> args <+> char '=' <+> body <> semi
  where
    typesig | null vars = text "unit"
            | otherwise = parens (hcat $ punctuate comma $ map snd vars)
    args | null vars = parens (text "dummy")
         | otherwise = parens (hcat $ punctuate comma $ map fst vars)

prettyType :: TypeRep a -> Doc
prettyType UnitType            = text "unit"
prettyType BoolType            = text "bool"
prettyType (IntType U NNative) = text "nat"
prettyType (IntType S NNative) = text "int"
prettyType (ArrayType t)       = char 'L' <> parens (prettyType t)

showVar :: VarId -> Doc
showVar v = char 'v' <> text (show v)

-- * Runtime system
--
runtime :: Doc
runtime = vcat [getLength (text "nat"), getIx (text "nat")]
  where
    getLength typ = let name = text "getLength_" <> typ
                     in prettyFun name [(text "arr",char 'L' <> parens typ)] (text "nat")
                          (text "match" <+> text "arr" <+> text "with"
                                         $$ match (text "nil    ") (char '0')
                                         $$ match (text "(z::zs)") (text "1 +" <+> name <+> text "zs"))
    getIx typ = let name = text "getIx_" <> typ
                 in prettyFun name [(text "arr",char 'L' <> parens typ), (text "ix", text "nat")] typ
                      (text "match arr with"
                        $$ match (text "nil    ") (char '0') -- TODO
                        $$ match (text "(z::zs)") (text "match ix with"
                                                        $$ match (text "0  ") (char 'z')
                                                        $$ match (text "n+1") (name <+> text "(zs, n)"))) 

