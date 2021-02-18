{-|
Copyright   : (C) 2020 QBayLogic B.V.
License     : BSD2 (see the file LICENSE)
Maintainer  : QBayLogic B.V. <devops@qbaylogic.com>

The AsTerm class and relevant instances for the partial evaluator. This
defines how to convert normal forms back into Terms which can be given as the
result of evaluation.
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.Core.PartialEval.AsTerm
  ( AsTerm(..)
  ) where

import Data.Bifunctor (first, second)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Clash.Core.FreeVars (localFVsOfTerms)
import Clash.Core.PartialEval.NormalForm
import Clash.Core.Term (Term(..), LetBinding, Pat, Alt, mkApps)
import Clash.Core.Var (Id)
import Clash.Core.VarEnv (VarSet, nullVarSet, elemVarSet)

-- | Convert a term in some normal form back into a Term. This is important,
-- as it may perform substitutions which have not yet been performed (i.e. when
-- converting from WHNF where heads contain the environment at that point).
--
class AsTerm a where
  asTerm:: a -> Term

instance (AsTerm a) => AsTerm (Neutral a) where
  asTerm = \case
    NeVar i -> Var i
    NePrim pr args -> mkApps (Prim pr) (argsToTerms args)
    NeApp x y -> App (asTerm x) (asTerm y)
    NeTyApp x ty -> TyApp (asTerm x) ty
    NeLetrec bs x ->
      let bs' = fmap (second asTerm) bs
          x'  = asTerm x
       in Letrec bs' x'

    NeCase x ty alts -> Case (asTerm x) ty (altsToTerms alts)

instance AsTerm Value where
  asTerm = \case
    VNeutral neu -> asTerm neu
    VLiteral lit -> Literal lit
    VData dc args env ->
      let term = mkApps (Data dc) (argsToTerms args)
       in bindEnv term env
    VLam i x env ->
      let term = Lam i x
       in bindEnv term env
    VTyLam i x env ->
      let term = TyLam i x
       in bindEnv term env
    VCast x a b -> Cast (asTerm x) a b
    VTick x tick -> Tick tick (asTerm x)
    VThunk x env -> bindEnv x env
   where
    bindEnv :: Term -> LocalEnv -> Term
    bindEnv x env =
      let fvs = localFVsOfTerms [x]
          binds = go [] fvs (lenvValues env)
       in if null binds then x else Letrec (go [] fvs (lenvValues env)) x

    go :: [LetBinding] -> VarSet -> Map Id Value -> [LetBinding]
    go acc fvs bindings
      | nullVarSet fvs = acc
      | otherwise =
          let (used, rest) = Map.partitionWithKey (\k _ -> k `elemVarSet` fvs) bindings
              used' = Map.toList (fmap asTerm used)
              fvs' = localFVsOfTerms (fmap snd used')
           in go (acc <> used') fvs' rest

instance AsTerm Normal where
  asTerm = \case
    NNeutral neu -> asTerm neu
    NLiteral lit -> Literal lit
    NData dc args -> mkApps (Data dc) (argsToTerms args)
    NLam i x -> Lam i (asTerm x)
    NTyLam i x -> TyLam i (asTerm x)
    NCast x a b -> Cast (asTerm x) a b
    NTick x tick -> Tick tick (asTerm x)

argsToTerms :: (AsTerm a) => Args a -> Args Term
argsToTerms = fmap $ first asTerm

altsToTerms :: (AsTerm a) => [(Pat, a)] -> [Alt]
altsToTerms = fmap $ second asTerm
