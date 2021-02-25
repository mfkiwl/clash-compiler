{-|
Copyright   : (C) 2020, QBayLogic B.V.
License     : BSD2 (see the file LICENSE)
Maintainer  : QBayLogic B.V. <devops@qbaylogic.com>

Normal forms for the partial evaluator. These provide a restricted model of
how terms can be constructed (compared to the more liberal Term type) which
give a stronger guarantee that evaluation does not produce invalid results.
This module is only needed to define new evaluators, for calling an existing
evaluator see Clash.Core.PartialEval.
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Clash.Core.PartialEval.NormalForm
  ( Arg
  , Args
  , Neutral(..)
  , Value(..)
  , collectValueApps
  , mkValueTicks
  , stripValue
  , collectValueTicks
  , isUndefined
  , Normal(..)
  , LocalEnv(..)
  , GlobalEnv(..)
  , workFreeCache
  ) where

import Control.Concurrent.Supply (Supply)
import Control.Lens (Lens', lens)
import Data.IntMap.Strict (IntMap)
import Data.Map.Strict (Map)

import Clash.Core.DataCon (DataCon)
import Clash.Core.Literal
import Clash.Core.Term (Term(..), PrimInfo(..), TickInfo, Pat)
import Clash.Core.TyCon (TyConMap)
import Clash.Core.Type (Type, TyVar)
import Clash.Core.Var (Id)
import Clash.Core.VarEnv (VarEnv, InScopeSet)
import Clash.Driver.Types (Binding(..))

-- | An argument applied to a function / data constructor / primitive.
--
type Arg a = Either a Type
type Args a = [Arg a]

-- | Neutral terms cannot be reduced, as they represent things like variables
-- which are unknown, partially applied functions, or case expressions where
-- the subject cannot be inspected. Consider:
--
-- v              Stuck if "v" is a free variable
-- p x1 ... xn    Stuck if "p" is a primitive that cannot be reduced
-- x $ y          Stuck if "x" is not known to be a lambda
-- x @ A          Stuck if "x" is not known to be a type lambda
-- case x of ...  Stuck if "x" is neutral (cannot choose an alternative)
--
-- Neutral terms can also be let expressions which preserve required bindings
-- in the normal form representation. Examples of bindings that may be kept are
-- bindings which perform work (and should not be copied) or bindings that
-- are recursive and are still referred to by the body of the let expression.
--
-- let ... in ... Preserved bindings are needed by the body
--
data Neutral a
  = NeVar    !Id
  | NePrim   !PrimInfo !(Args a)
  | NeApp    !(Neutral a) !a
  | NeTyApp  !(Neutral a) !Type
  | NeLetrec ![(Id, a)] !a
  | NeCase   !a !Type ![(Pat, a)]
  deriving (Show)

-- | A term which has been potentially evaluated to WHNF. If evaluation has
-- occurred, then there will be no redexes at the head of the Value, but
-- sub-terms may still have redexes. Data constructors are only considered to
-- be values when fully applied, if partially applied they should be
-- eta-expanded during evaluation.
--
-- Thunks are included so that lazy evaluation can be modelled without needing
-- to store Either Term Value in the environment. This makes the presentation
-- simpler, with the caveat that values must be forced when they are required
-- to not be thunks.
--
data Value
  = VNeutral  !(Neutral Value)
  | VLiteral  !Literal
  | VData     !DataCon !(Args Value) !LocalEnv
  | VLam      !Id !Term !LocalEnv
  | VTyLam    !TyVar !Term !LocalEnv
  | VCast     !Value !Type !Type
  | VTick     !Value !TickInfo
  | VThunk    !Term !LocalEnv
  deriving (Show)

collectValueApps :: Value -> Maybe (Neutral Value, Args Value)
collectValueApps (VNeutral n) = Just (go [] n)
 where
  go !args = \case
    NeApp x y -> go (Left y : args) x
    NeTyApp x ty -> go (Right ty : args) x
    neu -> (neu, args)

collectValueApps (VTick x _) = collectValueApps x
collectValueApps _ = Nothing

mkValueTicks :: Value -> [TickInfo] -> Value
mkValueTicks = foldl VTick

stripValue :: Value -> Value
stripValue = fst . collectValueTicks

collectValueTicks :: Value -> (Value, [TickInfo])
collectValueTicks = go []
 where
  go !acc = \case
    VTick v tick -> go (tick : acc) v
    value -> (value, acc)

isUndefined :: Value -> Bool
isUndefined = \case
  VNeutral (NePrim pr _) ->
    primName pr `elem`
      [ "Control.Exception.Base.absentError"
      , "Control.Exception.Base.patError"
      , "EmptyCase"
      , "GHC.Err.undefined"
      , "Clash.Transformations.undefined"
      , "Clash.XException.errorX"
      ]

  VNeutral (NeApp n _) ->
    isUndefined (VNeutral n)

  VNeutral (NeTyApp n _) ->
    isUndefined (VNeutral n)

  VTick value _ -> isUndefined value
  VCast value _ _ -> isUndefined value

  _ -> False

-- | A term which is in beta-normal eta-long form (NF). This has no redexes,
-- and all partially applied functions in sub-terms are eta-expanded.
--
data Normal
  = NNeutral  !(Neutral Normal)
  | NLiteral  !Literal
  | NData     !DataCon !(Args Normal)
  | NLam      !Id !Normal
  | NTyLam    !TyVar !Normal
  | NCast     !Normal !Type !Type
  | NTick     !Normal !TickInfo
  deriving (Show)

data LocalEnv = LocalEnv
  { lenvTypes :: Map TyVar Type
    -- ^ Local type environment. These are types that are introduced while
    -- evaluating the current term (i.e. by type applications)
  , lenvValues :: Map Id Value
    -- ^ Local term environment. These are WHNF terms or unevaluated thunks
    -- introduced while evaluating the current term (i.e. by applications)
  , lenvInScope :: InScopeSet
    -- ^ The set of in scope variables during partial evaluation. This includes
    -- new variables introduced by the evaluator (such as the ids of binders
    -- introduced during eta expansion.)
  , lenvFuel :: Word
    -- ^ The amount of fuel left in the local environment when the previous
    -- head was reached. This is needed so resuming evaluation does not lead
    -- to additional fuel being available.
  }

instance Show LocalEnv where
  show = const "<env>"
{-
  show (LocalEnv ts vs f) = mconcat
    [ "LocalEnv{"
    , "lenvTypes="
    , show ts
    , ",lenvValues="
    , show vs
    , ",lenvFuel="
    , show f
    , "}"
    ]
-}

-- TODO Add recursion info to the binding map. Until then we are forced to
-- spend fuel on non-recursive (terminating) terms. Later it would save us from
-- calling termination analysis on non-recursive terms.

data GlobalEnv = GlobalEnv
  { genvBindings :: VarEnv (Binding Value)
    -- ^ Global term environment. These are the potentially evaluated bodies
    -- of the top level definitions which are forced on lookup.
  , genvTyConMap :: TyConMap
    -- ^ The type constructors known about by Clash.
  , genvSupply :: Supply
    -- ^ The supply of fresh names for generating identifiers.
  , genvFuel :: Word
    -- ^ The remaining fuel which can be spent inlining global variables. This
    -- is saved in the local environment, so when evaluation resumes from WHNF
    -- the amount of fuel used is preserved.
  , genvHeap :: IntMap Value
    -- ^ The heap containing the results of any evaluated IO primitives.
  , genvAddr :: Int
    -- ^ The address of the next element to be inserted into the heap.
  , genvIsSubject :: Bool
    -- ^ Whether the evalatuor currently in the subject of a case expression,
    -- or evaluating a term to be inlined as part of the subject. If this is
    -- true, the following changes apply to ensure maximum opportunities for
    -- case of known constructor to fire:
    --
    --   * data constructors for boxed types (e.g. I#) are preserved rather
    --   than being converted back into their corresponding primitives
    --
    --   * identifiers in the local environment which refer to something which
    --   performs work are inlined, as this may result in removing the work
  , genvWorkCache :: VarEnv Bool
    -- ^ Cache for the results of isWorkFree. This is required to use
    -- Clash.Rewrite.WorkFree.isWorkFree.
  }

workFreeCache :: Lens' GlobalEnv (VarEnv Bool)
workFreeCache = lens genvWorkCache (\env x -> env { genvWorkCache = x })
