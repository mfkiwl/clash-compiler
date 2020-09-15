{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Primitive.Enum
  ( enumPrims
  ) where

import Control.Monad.Catch (throwM)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import qualified Data.List as List (find)
import Data.Text (Text)

import Clash.Core.DataCon
import Clash.Core.Term
import Clash.Core.Type
import Clash.Core.PartialEval.Monad
import Clash.Core.PartialEval.NormalForm

import {-# SOURCE #-} Clash.GHC.PartialEval.Eval
import Clash.GHC.PartialEval.Primitive.FromAst
import Clash.GHC.PartialEval.Primitive.Info
import Clash.GHC.PartialEval.Primitive.Strategy
import Clash.GHC.PartialEval.Primitive.ToAst
import Clash.GHC.PartialEval.Primitive.Unboxed

import Clash.Debug -- TODO

enumPrims :: HashMap Text PrimImpl
enumPrims = HashMap.fromList
  [ ("GHC.Prim.dataToTag#", primDataToTag)
  , ("GHC.Prim.tagToEnum#", primTagToEnum)
  ]

primDataToTag :: PrimImpl
primDataToTag _ pr args
  | [Right ty, Left x] <- args
  = do value <- forceEval x
       resTy <- resultType pr args
       go value resTy

  | otherwise
  = empty
 where
  go :: Value -> Type -> Eval Value
  go value ty =
    case value of
      VNeutral _ -> empty
      VData dc _ _ -> toValue (UInt (dcTag dc)) ty
      VTick x _ -> go x ty
      _ -> throwM ResultUndefined

primTagToEnum :: PrimImpl
primTagToEnum e _ args
  | [Right ty, Left x] <- args
  = do env <- getLocalEnv
       dcs <- resultDataCons ty
       UInt a <- fromValueForce x

       case List.find (\dc -> dcTag dc == a + 1) dcs of
         Just dc -> pure (VThunk (Data dc) env)
         _ -> empty

  | otherwise
  = empty
