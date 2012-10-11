module Examples where

import PrettyRAML

import qualified Prelude

import Feldspar
import Feldspar.Vector

-- * Test expressions

expr1 :: Data Index
expr1 = 1 + (2 * 5)

expr2 :: Data Index -> Data Index
expr2 x = 1 + x

expr3 :: Data Index -> Data [Index]
expr3 l = parallel l $ const l

expr4 :: Vector1 Index -> Data Index
expr4 = sum

