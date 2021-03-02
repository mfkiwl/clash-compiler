{-|
Copyright   : (C) 2020, QBayLogic B.V.
License     : BSD2 (see the file LICENSE)
Maintainer  : QBayLogic B.V. <devops@qaylogic.com>

Check whether a term is work free or not. This is used by transformations /
evaluation to check whether it is possible to perform changes without
duplicating work in the result, e.g. inlining.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Clash.Rewrite.WorkFree
  ( isWorkFree
  , isWorkFreeBinder
  , isWorkFreeClockOrResetOrEnable
  , isWorkFreeIsh
  , isConstant
  , isConstantNotClockReset
  , isExpandable
  ) where

import Control.Lens (Lens')
import Control.Monad.Extra (allM, andM, eitherM)
import Control.Monad.State.Class (MonadState)
import Data.Either (lefts)
import GHC.Stack (HasCallStack)

import Clash.Core.FreeVars
import Clash.Core.Pretty (showPpr)
import Clash.Core.Term
import Clash.Core.TermInfo
import Clash.Core.TyCon (TyConMap)
import Clash.Core.Type (isPolyFunTy)
import Clash.Core.Util
import Clash.Core.Var (Id, Var(..), isLocalId)
import Clash.Core.VarEnv (VarEnv, lookupVarEnv)
import Clash.Driver.Types (BindingMap, Binding(..))
import Clash.Util (makeCachedU)

-- | Determines whether a global binder is work free. Errors if binder does
-- not exist.
isWorkFreeBinder
  :: (HasCallStack, MonadState s m)
  => Lens' s (VarEnv Bool)
  -> BindingMap
  -> Id
  -> m Bool
isWorkFreeBinder cache bndrs bndr =
  makeCachedU bndr cache $
    case lookupVarEnv bndr bndrs of
      Nothing -> error ("isWorkFreeBinder: couldn't find binder: " ++ showPpr bndr)
      Just (bindingTerm -> t) ->
        if bndr `globalIdOccursIn` t
        then pure False
        else isWorkFree cache bndrs t

{-# INLINABLE isWorkFree #-}
-- | Determine whether a term does any work, i.e. adds to the size of the
-- circuit. This function requires a cache (specified as a lens) to store the
-- result for querying work info of global binders.
--
isWorkFree
  :: forall s m
   . (MonadState s m)
  => Lens' s (VarEnv Bool)
  -> BindingMap
  -> Term
  -> m Bool
isWorkFree cache bndrs = go True
 where
  -- If we are in the outermost level of a term (i.e. not checking a subterm)
  -- then a term is work free if it simply refers to a local variable. This
  -- does not apply to subterms, as we do not want to count expressions like
  --
  --   f[LocalId] x[LocalId]
  --
  -- as being work free, as the term bound to f may introduce work.
  --
  go :: Bool -> Term -> m Bool
  go isOutermost (collectArgs -> (fun, args)) =
    case fun of
      Var i
        -- We only allow polymorphic / function typed variables to be inlined
        -- if they are locally scoped, and the term is only a variable.
        --
        -- TODO This could be improved later by passing an InScopeSet to
        -- isWorkFree with all the local FVs of the term being checked. PE
        -- would need to be changed to know the FVs of global binders first.
        --
        | isPolyFunTy (varType i) ->
            pure (isLocalId i && isOutermost && null args)
        | isLocalId i ->
            pure True
        | otherwise ->
            andM [isWorkFreeBinder cache bndrs i, allM goArg args]

      Data _ -> allM goArg args
      Literal _ -> pure True
      Prim pr ->
        case primWorkInfo pr of
          -- We can ignore arguments because the primitive outputs a constant
          -- regardless of their values.
          WorkConstant -> pure True
          WorkNever -> allM goArg args
          WorkVariable -> pure (all isConstantArg args)
          WorkAlways -> pure False

      Lam _ e -> andM [go False e, allM goArg args]
      TyLam _ e -> andM [go False e, allM goArg args]
      Letrec bs e -> andM [go False e, allM (go False . snd) bs, allM goArg args]
      Case s _ [(_, a)] -> andM [go False s, go False a, allM goArg args]
      Case e _ _ -> andM [go False e, allM goArg args]
      _ -> pure False

  goArg e = eitherM (go False) (pure . const True) (pure e)
  isConstantArg = either isConstant (const True)

-- | Determine if a term represents a constant
isConstant :: Term -> Bool
isConstant e = case collectArgs e of
  (Data _, args)   -> all (either isConstant (const True)) args
  (Prim _, args) -> all (either isConstant (const True)) args
  (Lam _ _, _)     -> not (hasLocalFreeVars e)
  (Literal _,_)    -> True
  _                -> False

isConstantNotClockReset :: TyConMap -> Term -> Bool
isConstantNotClockReset tcm e
  | isClockOrReset tcm eTy =
      case fst (collectArgs e) of
        Prim pr -> primName pr == "Clash.Transformations.removedArg"
        _ -> False

  | otherwise = isConstant e
 where
  eTy = termType tcm e

-- TODO: Remove function after using WorkInfo in 'isWorkFreeIsh'
isWorkFreeClockOrResetOrEnable
  :: TyConMap
  -> Term
  -> Maybe Bool
isWorkFreeClockOrResetOrEnable tcm e =
  let eTy = termType tcm e in
  if isClockOrReset tcm eTy || isEnable tcm eTy then
    case collectArgs e of
      (Prim p,_) -> Just (primName p == "Clash.Transformations.removedArg")
      (Var _, []) -> Just True
      (Data _, []) -> Just True -- For Enable True/False
      (Literal _,_) -> Just True
      _ -> Just False
  else
    Nothing

-- | A conservative version of 'isWorkFree'. Is used to determine in 'bindConstantVar'
-- to determine whether an expression can be "bound" (locally inlined). While
-- binding workfree expressions won't result in extra work for the circuit, it
-- might very well cause extra work for Clash. In fact, using 'isWorkFree' in
-- 'bindConstantVar' makes Clash two orders of magnitude slower for some of our
-- test cases.
--
-- In effect, this function is a version of 'isConstant' that also considers
-- references to clocks and resets constant. This allows us to bind
-- HiddenClock(ResetEnable) constructs, allowing Clash to constant spec
-- subconstants - most notably KnownDomain. Doing that enables Clash to
-- eliminate any case-constructs on it.
isWorkFreeIsh
  :: TyConMap
  -> Term
  -> Bool
isWorkFreeIsh tcm e =
  case isWorkFreeClockOrResetOrEnable tcm e of
    Just b -> b
    Nothing ->
      case collectArgs e of
        (Data _, args)     -> all isWorkFreeIshArg args
        (Prim pInfo, args) -> case primWorkInfo pInfo of
          WorkAlways   -> False -- Things like clock or reset generator always
                                       -- perform work
          WorkVariable -> all isConstantArg args
          _            -> all isWorkFreeIshArg args

        (Lam _ _, _)       -> not (hasLocalFreeVars e)
        (Literal _,_)      -> True
        _                  -> False
 where
  isWorkFreeIshArg = either (isWorkFreeIsh tcm) (const True)
  isConstantArg    = either isConstant (const True)

-- | An expression is expandable if it can be duplicated when evaluating the
-- subject of a case expression. The only expressions considered to be
-- expandable are those which could lead to case-of-constructor being applied.
--
isExpandable :: BindingMap -> Term -> Bool
isExpandable bndrs = go
 where
  goArgs = all go . lefts
  goBndr = go . bindingTerm
  goAlts = all go . fmap snd

  go (collectArgs -> (f, args)) =
    case f of
      Var i
        | isLocalId i -> goArgs args
        | otherwise -> maybe False goBndr (lookupVarEnv i bndrs) && goArgs args

      Data _ -> goArgs args
      Literal _ -> True
      Prim pr ->
        -- There isn't any point inlining a primitive which does not correspond
        -- to a literal which can be matched against.
        primName pr `elem`
          [ -- Clash builtin types
            "Clash.Sized.Internal.BitVector.fromInteger##"
          , "Clash.Sized.Internal.BitVector.fromInteger#"
          , "Clash.Sized.Internal.Index.fromInteger#"
          , "Clash.Sized.Internal.Signed.fromInteger#"
          , "Clash.Sized.Internal.Unsigned.fromInteger#"
            -- GHC builtin types
          , "GHC.Types.C#"
          , "GHC.Types.D#"
          , "GHC.Types.F#"
          , "GHC.Types.I#"
          , "GHC.Types.I8#"
          , "GHC.Types.I16#"
          , "GHC.Types.I32#"
          , "GHC.Types.I64#"
          , "GHC.Types.W#"
          , "GHC.Types.W8#"
          , "GHC.Types.W16#"
          , "GHC.Types.W32#"
          , "GHC.Types.W64#"
            -- Empty primtives
          , "_CO_"
          , "_TY_"
          ] <> undefinedPrims && goArgs args

      Lam _ x -> go x && goArgs args
      TyLam _ x -> go x && goArgs args
      Letrec _ x -> go x
      Case x _ alts -> go x && goAlts alts
      Tick _ x -> go x && goArgs args
      _ -> False
