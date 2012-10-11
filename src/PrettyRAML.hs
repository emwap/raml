{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances #-}

module PrettyRAML where

import Language.Syntactic
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

class Pretty sub
  where
    prettySym :: Pretty dom => sub sig -> Args (AST dom) a -> Doc

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

pretty :: (Pretty dom) => ASTF dom a -> Doc
pretty = simpleMatch prettySym

toRAML :: SyntacticFeld a => a -> Doc
toRAML = go [] . reifyFeld N32
  where
    go :: [(VarId,Doc)] -> ASTF (Decor Info FeldDomain) a -> Doc
    go vars (Sym (Decor info lam) :$ body)
        | Just (SubConstr2 (Lambda v)) <- prjLambda lam
        = go ((v,prettyType $ argType $ infoType info):vars) body
    go vars body =  name <+> char ':' <+> typesig <+> text "->" <+> bodytype
                 $$ name <> args <+> char '=' <+> pretty body <> semi
                 $$ text "main = ()"
              
      where
        name    = text "test"
        typesig | null vars = text "unit"
                | otherwise = parens (hcat $ punctuate comma $ map snd $ reverse vars)
        args | null vars = parens (text "dummy")
             | otherwise = parens (hcat $ punctuate comma $ map (showVar . fst) $ reverse vars)
        bodytype = prettyType (infoType $ getInfo body)

instance Pretty (NUM :|| Type)
  where
    prettySym (C' Add) (a :* b :* Nil) = parens $ pretty a <+> char '+' <+> pretty b
    prettySym (C' Sub) (a :* b :* Nil) = parens $ pretty a <+> char '-' <+> pretty b
    prettySym (C' Mul) (a :* b :* Nil) = parens $ pretty a <+> char '*' <+> pretty b

instance Pretty (Literal :|| Type)
  where
    prettySym (C' (Literal l)) Nil = char '+' <> text (show l)

instance Pretty (Variable :|| Type)
  where
    prettySym (C' (Variable v)) Nil = showVar v

prettyType :: TypeRep a -> Doc
prettyType UnitType            = text "unit"
prettyType BoolType            = text "bool"
prettyType (IntType U NNative) = text "int"
prettyType (ArrayType t)       = char 'L' <> parens (prettyType t)

showVar :: VarId -> Doc
showVar v = char 'v' <> text (show v)

-- * Test expressions

expr1 :: Data Index
expr1 = 1 + (2 * 5)

expr2 :: Data Index -> Data Index
expr2 x = 1 + x

