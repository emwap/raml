{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module SimpleAST where



import Data.Dynamic hiding (TypeRep)
import Data.Foldable
import Data.Traversable

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Constructs.Decoration
import Language.Syntactic.Constructs.Literal

import Feldspar.Core.Types
import Feldspar.Core.Interpretation
import Feldspar.Core.Constructs
import Feldspar.Core.Constructs.Array
import Feldspar.Core.Constructs.Binding
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
import Feldspar



----------------------------------------------------------------------------------------------------
-- * Simple representation of Feldspar core
----------------------------------------------------------------------------------------------------

type Name = String

data Typ
    = IntType
    | OtherType
  deriving (Prelude.Eq, Show)

data Feld = Feld
    { feldExpr :: F Feld
    , feldType :: Typ
    }
  deriving (Show)

data F e
    = Lit String Dynamic
    | PrimFun Name [e]
    | Var VarId
    | Cond e e e
    | Par VarId e e
  deriving (Show, Functor, Foldable, Traversable)



----------------------------------------------------------------------------------------------------
-- * Conversion
----------------------------------------------------------------------------------------------------

simplifyType :: TypeRep a -> Typ
simplifyType _ = OtherType

class Render sub => Simplify sub
  where
    simplifySym :: Simplify' dom => sub sig -> Args (AST (Decor Info dom)) a -> F Feld
    simplifySym s args = PrimFun (render s) (listArgs simplifyAST args)

class
    ( Project (CLambda Type) dom
    , Project (Variable :|| Type) dom
    , Simplify dom
    ) =>
      Simplify' dom

instance
    ( Project (CLambda Type) dom
    , Project (Variable :|| Type) dom
    , Simplify dom
    ) =>
      Simplify' dom

instance (Simplify sub1, Simplify sub2) => Simplify (sub1 :+: sub2)
  where
    simplifySym (InjL s) = simplifySym s
    simplifySym (InjR s) = simplifySym s

instance (Simplify sub) => Simplify (sub :|| pred)
  where
    simplifySym (C' s) = simplifySym s

instance (Simplify sub) => Simplify (Decor info sub)
  where
    simplifySym (Decor _ s) = simplifySym s

instance Render sym => Simplify sym

simplifyAST :: Simplify' dom => ASTF (Decor Info dom) a -> Feld
simplifyAST a = Feld (simpleMatch simplifySym a) (simplifyType $ infoType $ getInfo a)

simplifyTop :: Simplify' dom => ASTF (Decor Info dom) a -> Feld
simplifyTop (lam :$ body)
    | Just (SubConstr2 (Lambda v)) <- prjLambda lam
    = simplifyTop body
simplifyTop a = simplifyAST a

simplify :: SyntacticFeld a => a -> Feld
simplify = simplifyTop . reifyFeld defaultFeldOpts N32

instance Simplify (Literal :|| Type)
  where
    simplifySym (C' (Literal a)) Nil = Lit (show a) (toDyn a)

instance Simplify (Variable :|| Type)
  where
    simplifySym (C' (Variable v)) Nil = Var v

instance Simplify (Condition :|| Type)
  where
    simplifySym (C' Condition) (cond :* t :* f :* Nil) =
        Cond (simplifyAST cond) (simplifyAST t) (simplifyAST f)

instance Simplify (Array :|| Type)
  where
    simplifySym (C' Parallel) (len :* (lam :$ body) :* Nil)
      | Just (SubConstr2 (Lambda v)) <- prjLambda lam = Par v (simplifyAST len) (simplifyAST body)



----------------------------------------------------------------------------------------------------
-- * Test
----------------------------------------------------------------------------------------------------

expr1 a = parallel a (*2)

