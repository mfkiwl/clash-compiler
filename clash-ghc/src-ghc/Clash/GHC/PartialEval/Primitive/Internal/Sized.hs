{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}

module Clash.GHC.PartialEval.Primitive.Internal.Sized where

import Control.Exception (ArithException, evaluate)
import Control.Monad.Catch (throwM, try)
import Control.Monad.IO.Class (liftIO)
import Data.Proxy
import Data.Reflection (reifyNat)
import GHC.TypeLits (KnownNat)

import Clash.XException (maybeIsX)

import Clash.Core.PartialEval.Monad
import Clash.Core.PartialEval.NormalForm

import Clash.GHC.PartialEval.Primitive.FromAst
import Clash.GHC.PartialEval.Primitive.Info
import Clash.GHC.PartialEval.Primitive.Strategy
import Clash.GHC.PartialEval.Primitive.ToAst

-- | Lift a primitive that represents some constant value in a sized type.
-- Examples of this are undefined#, or minBound# / maxBound#.
--
liftNullarySized
  :: forall f
   . (forall size. (KnownNat size) => ToAst (f size))
  => (forall n. (KnownNat n) => f n)
  -> PrimImpl
liftNullarySized f _ p args
  | [Right n] <- args
  = do sz <- typeSize n Nothing
       reifyNat sz go

  | [Right n, Left knN] <- args
  = do sz <- typeSize n (Just knN)
       reifyNat sz go

  | otherwise
  = empty
 where
  go :: forall m. (KnownNat m) => Proxy m -> Eval Value
  go Proxy = resultType p args >>= toValue @(f m) f

-- | Lift a primitive that represents some unary function over a sized type.
-- Examples of this are complement# and negate#.
--
liftUnarySized
  :: forall f
   . ( forall size. FromAst (f size)
     , forall size. ToAst (f size)
     )
  => (forall n. (KnownNat n) => f n -> f n)
  -> PrimImpl
liftUnarySized f e p args
  | [Right n, Left x] <- args
  = do sz <- typeSize n Nothing
       reifyNat sz (\proxy -> go proxy x)

  | [Right n, Left knN, Left x] <- args
  = do sz <- typeSize n (Just knN)
       reifyNat sz (\proxy -> go proxy x)

  | otherwise
  = empty
 where
  go :: forall m. (KnownNat m) => Proxy m -> Value -> Eval Value
  go Proxy x = do
    a <- fromValueForce @(f m) x
    resTy <- resultType p args
    result <- try @_ @ArithException (liftIO $ evaluate $ maybeIsX (f a))

    case result of
      Right (Just r) -> toValue @(f m) r resTy
      _ -> throwM ResultUndefined

-- | Lift a primitive that represents some binary function over a sized type.
-- Examples of this are (+), (*) and xor.
--
liftBinarySized
  :: forall f
   . ( forall size. FromAst (f size)
     , forall size. ToAst (f size)
     )
  => (forall n. (KnownNat n) => f n -> f n -> f n)
  -> PrimImpl
liftBinarySized f e p args
  | [Right n, Left x, Left y] <- args
  = do sz <- typeSize n Nothing
       reifyNat sz (\proxy -> go proxy x y)

  | [Right n, Left knN, Left x, Left y] <- args
  = do sz <- typeSize n (Just knN)
       reifyNat sz (\proxy -> go proxy x y)

  | otherwise
  = empty
 where
  go :: forall m. (KnownNat m) => Proxy m -> Value -> Value -> Eval Value
  go Proxy x y = do
    a <- fromValueForce @(f m) x
    b <- fromValueForce @(f m) y
    resTy <- resultType p args
    result <- try @_ @ArithException (liftIO $ evaluate $ maybeIsX (f a b))

    case result of
      Right (Just r) -> toValue @(f m) r resTy
      _ -> throwM ResultUndefined

liftComparison
  :: forall f
   . (forall size. FromAst (f size))
  => (forall n. (KnownNat n) => f n -> f n -> Bool)
  -> PrimImpl
liftComparison f e p args
  | [Right n, Left x, Left y] <- args
  = do sz <- typeSize n Nothing
       reifyNat sz (\proxy -> go proxy x y)

  | [Right n, Left knN, Left x, Left y] <- args
  = do sz <- typeSize n (Just knN)
       reifyNat sz (\proxy -> go proxy x y)

  | otherwise
  = empty
 where
  go :: forall m. (KnownNat m) => Proxy m -> Value -> Value -> Eval Value
  go Proxy x y = do
    a <- fromValueForce @(f m) x
    b <- fromValueForce @(f m) y
    resTy <- resultType p args
    toValue (f a b) resTy
