{-# LANGUAGE LambdaCase #-}

module Clash.GHC.PartialEval.Primitive.Strategy
  ( PrimImpl
  , liftId
  , liftNullary
  , liftUnary
  , liftBinary
  , liftBox -- TODO remove, prims are kept so this is liftId
  , liftUndefined
  , coreUnfolding
  , tryArith
    -- Re-exported
  , Alternative(..)
  ) where

import Control.Applicative (Alternative(..))
import Control.Exception (ArithException, evaluate)
import Control.Monad (foldM)
import Control.Monad.Catch (throwM, try)
import Control.Monad.IO.Class (liftIO)
import Data.Either (lefts)
import GHC.Stack (HasCallStack)

import Clash.Core.Name (nameOcc)
import Clash.Core.PartialEval.Monad
import Clash.Core.PartialEval.NormalForm
import Clash.Core.Term (Term(Var), PrimInfo(..))
import Clash.Core.Var (varName)

import {-# SOURCE #-} Clash.GHC.PartialEval.Eval
import Clash.GHC.PartialEval.Primitive.FromAst
import Clash.GHC.PartialEval.Primitive.Info
import Clash.GHC.PartialEval.Primitive.ToAst

import Clash.Debug -- TODO

type PrimImpl = (Term -> Eval Value) -> PrimInfo -> Args Value -> Eval Value

-- | The primitive should not be implemented as it is unsafe to do so. Using
-- this rule does not change the behaviour of the evaluator, but does suppress
-- the "no implementation" message when running in debug mode.
--
liftId :: (HasCallStack) => PrimImpl
liftId _ pr args = pure (VNeutral (NePrim pr args))

-- | The primitive takes no arguments, and has an implementation that is
-- available at run-time which can be lifted into Eval.
--
liftNullary :: (HasCallStack, ToAst a) => a -> PrimImpl
liftNullary result _eval pr args =
  case lefts args of
    [] -> do
      resTy <- resultType pr args
      toValue result resTy

    _ -> empty

-- | Lift a unary function to an implemenatation for a primitive operation.
-- This is used for primitives where the evaluation does not differ from the
-- semantics of the underlying Haskell implemenatation.
--
liftUnary :: (HasCallStack, FromAst a, ToAst b) => (a -> b) -> PrimImpl
liftUnary f _eval pr args =
  case lefts args of
    [x] -> do
      a <- fromValueForce x
      resTy  <- resultType pr args
      result <- try @_ @ArithException (liftIO $ evaluate (f a))

      case result of
        Left _e -> throwM ResultUndefined
        Right r -> toValue r resTy

    _ -> empty

-- | Lift a binary function to an implementation for a primitive operation.
-- See liftUnary for more information.
--
liftBinary
  :: (HasCallStack, FromAst a, FromAst b, ToAst c, Show a, Show b)
  => (a -> b -> c)
  -> PrimImpl
liftBinary f _eval pr args =
  case lefts args of
    [x, y] -> do
      xV <- fromValueForce x
      yV <- fromValueForce y
      resTy  <- resultType pr args
      result <- try @_ @ArithException (liftIO $ evaluate (f xV yV))

      case result of
        Left _e -> throwM ResultUndefined
        Right r -> toValue r resTy

    _ -> empty

-- | Lift a constructor for a boxed type, e.g. I# for Int. Attempting to use
-- this function on other constructors may fail as it expects a unary
-- constructor.
--
-- TODO Replace with liftUnary# ?
--
liftBox :: (HasCallStack) => PrimImpl
liftBox _eval pr args =
  case args of
    [Left x] -> do
      [boxDc] <- resultDataCons (primType pr)
      VData boxDc [Left x] <$> getLocalEnv

    _ -> empty

liftUndefined :: (HasCallStack) => PrimImpl
liftUndefined _ _ _ = throwM ResultUndefined

-- | Try to evaluate an arithmetic primtive which may throw an ArithException.
-- These cannot be caught with catch, so we use try and rethrow ResultUndefined.
--
tryArith :: PrimImpl -> PrimImpl
tryArith impl e pr args = do
  result <- try @_ @ArithException (impl e pr args)

  case result of
    Left _e -> throwM ResultUndefined
    Right x -> pure x

-- | Evaluate the primitive using the core for the primitive if available.
-- This does not work for primitives with no available implementation (such as
-- wired in GHC primitives) or primitives where the core unfolding cannot be
-- evaluated by the evaluator (such as unfoldings that use unsafeCoerce).
--
coreUnfolding :: PrimImpl
coreUnfolding eval pr args = do
  fuel <- getFuel

  case primCoreId pr of
    Just c | fuel > 0 ->
      withFuel $ do
        core <- eval (Var c)
        result <- foldM applyArg core args
        pure (replaceRecursion pr result)

    _ -> pure (VNeutral (NePrim pr args))
 where
  applyArg val = either (apply val) (applyTy val)

-- | If the evaluator runs out of fuel, it may be left with a recursive call to
-- the primitive being evaluated. To avoid this, traverse the resulting value
-- and replace any recursive calls with a NePrim.
--
-- This assumes that the core unfolding for a primitive does not call
-- any other primtiives that rely on a core unfolding. If this turns out
-- to not be true, replaceRecursion would need to consider whether any
-- application represents a primitive call that is unfolded.
--
replaceRecursion :: PrimInfo -> Value -> Value
replaceRecursion pr = go
 where
  go = \case
    VCast v a b -> VCast (go v) a b
    VTick v tick -> VTick (go v) tick
    value ->
      case collectValueApps value of
        Just (NeVar i, args) ->
          if nameOcc (varName i) == primName pr
            then VNeutral (NePrim pr args)
            else value

        _ -> value
