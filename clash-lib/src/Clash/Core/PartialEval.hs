{-|
Copyright   : (C) 2020 QBayLogic B.V.
License     : BSD2 (see the file LICENSE)
Maintainer  : QBayLogic B.V. <devops@qbaylogic.com>

The main API of the partial evaluator. This exposes the main functions needed
to call the evaluator, and the type of evaluators. A concrete implementation
of an evaluator is required to use this module: this can be imported from the
library for the compiler front-end, e.g. Clash.GHC.PartialEval in clash-ghc.
-}

module Clash.Core.PartialEval where

import Control.Concurrent.Supply (Supply)
import Data.IntMap.Strict (IntMap)

import Clash.Core.PartialEval.AsTerm
import Clash.Core.PartialEval.Monad
import Clash.Core.PartialEval.NormalForm
import Clash.Core.Term (Term)
import Clash.Core.TyCon (TyConMap)
import Clash.Core.VarEnv (InScopeSet)
import Clash.Driver.Types (Binding(..), BindingMap)

-- | An evaluator for Clash core. This consists of two functions: one to
-- evaluate a term to weak-head normal form (WHNF) and another to recursively
-- evaluate sub-terms to obtain beta-normal eta-long form (NF).
--
data Evaluator = Evaluator
  { evalWhnf :: Term  -> Eval Value
  , quoteNf  :: Value -> Eval Normal
  }

-- | Evaluate a term to WHNF, converting the result back to a Term.
-- The global environment at the end of evaluation is also returned, callers
-- should preserve any parts of the global environment needed for later calls.
--
whnf
  :: Evaluator
  -- ^ The evaluator implementation to use.
  -> GlobalEnv
  -- ^ The initial global environment.
  -> Term
  -- ^ The term under evaluation.
  -> IO (Term, GlobalEnv)
  -- ^ The term evalated to WHNF, and the final global environment.
whnf e g x =
  let l = LocalEnv mempty mempty (genvFuel g)
   in runEval g l (asTerm <$> evalWhnf e x)

-- | Evaluate a term to NF, converting the result back to a Term.
-- See `whnf` for more details.
--
nf
  :: Evaluator
  -- ^ The evaluator implementation to use.
  -> GlobalEnv
  -- ^ The initial global environment.
  -> Term
  -- ^ The term under evaluation.
  -> IO (Term, GlobalEnv)
  -- ^ The term evalated to NF, and the final global environment.
nf e g x =
  let l = LocalEnv mempty mempty (genvFuel g)
   in do runEval g l (asTerm <$> (evalWhnf e x >>= quoteNf e))

mkGlobalEnv
  :: BindingMap
  -- ^ Global bindings available to the evaluator.
  -> TyConMap
  -- ^ The type constructors known by Clash.
  -> InScopeSet
  -- ^ The set of variables in scope during evaluation.
  -> Supply
  -- ^ The supply of fresh names for variables.
  -> Word
  -- ^ The initial supply of fuel.
  -> IntMap Value
  -- ^ The initial IO heap.
  -> Int
  -- ^ The address of the next heap element.
  -> Bool
  -- ^ Whether evaluation starts in the subject of a case expression.
  -> GlobalEnv
mkGlobalEnv bm tcm iss ids fuel heap addr isSubj =
  GlobalEnv (fmap asThunk bm) tcm iss ids fuel heap addr isSubj mempty
 where
  asThunk b@Binding{bindingTerm=term} =
    b { bindingTerm = VThunk term (LocalEnv mempty mempty fuel) }
