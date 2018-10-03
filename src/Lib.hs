{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module Lib where

import           Control.Monad        (join)
import           Control.Monad.Reader (ReaderT (..))
import           Data.Functor         (Functor)

newtype Id = Id Int deriving Show
newtype Value = Value Char deriving Show
newtype Result = Result [ChangeAccum] deriving Show
newtype ChangeAccum = ChangeAccum
    { unChangeAccum :: [(Id, Value)]
    } deriving Show

-- | Auxiliary function for testing of baseMModifyAccum
-- | Increment Id by one (I bet there is lens one-liner for this)
incRes :: Result -> [(Id, Value)]
incRes (Result res) = join (incIds <$> (unChangeAccum <$> res))
  where
    incIds :: [(Id, Value)] -> [(Id, Value)]
    incIds xs = incId <$> xs

    incId :: (Id, Value) -> (Id, Value)
    incId (Id i, value) = (Id (i+1), value)

-- | Core follows | --

data DbAccessM chgAccum id value res
    = DbModifyAccum [(id, value)] ([chgAccum] -> res)

data DbAccessActionsM chgAccum id value m = DbAccessActionsM
    { daaModifyAccum :: chgAccum -> [(id, value)] -> m [chgAccum]
    }

class DbActions (effect :: * -> *) (actions :: (* -> *) -> *) param (m :: * -> *) where
    -- | Execute @effect r@ using @actions m@ and return value @r@ in monad @m@.
    executeEffect :: effect r -> actions m -> param -> m r

instance Functor m => DbActions (DbAccessM chgAccum id value)
                                (DbAccessActionsM chgAccum id value) chgAccum m where
    executeEffect (DbModifyAccum chgSet cont) daaM chgAccum =
        cont <$> daaModifyAccum daaM chgAccum chgSet

class Monad m => Effectful eff m where
    -- | Executes effect `eff` in monad `m`.
    -- A natural transformation from effect data type to monad.
    effect :: eff a -> m a

type BaseMConstraint eff ctx m = ( Effectful eff m
                                 )

newtype BaseM eff ctx a = BaseM { unBaseM :: forall m . BaseMConstraint eff ctx m => m a }
    deriving Functor

instance HasGetter ctx (BaseMIOExec eff ctx) => Effectful eff (BaseMIO eff ctx) where
    effect eff = BaseMIO $ ReaderT $ \ctx -> unBaseMIOExec (gett ctx) ctx eff

instance Effectful eff (BaseM eff ctx) where
    effect eff = BaseM (effect eff)

instance Applicative (BaseM eff ctx) where
    pure a = BaseM $ pure a
    BaseM a <*> BaseM b = BaseM $ a <*> b

instance Monad (BaseM eff ctx) where
    a >>= b = BaseM $ unBaseM a >>= unBaseM . b

newtype BaseMIO (eff :: * -> *) ctx a = BaseMIO
    { unBaseMIO :: ReaderT ctx IO a }
    deriving (Functor)

deriving instance Applicative (BaseMIO eff ctx)
deriving instance Monad (BaseMIO eff ctx)

runBaseMIO
    :: forall eff ctx a .
    ( HasGetter ctx (BaseMIOExec eff ctx)
    )
    => BaseM eff ctx a
    -> ctx
    -> IO a
runBaseMIO bm ctx = runReaderT (unBaseMIO @eff $ unBaseM bm) ctx

newtype BaseMIOExec eff ctx = BaseMIOExec { unBaseMIOExec :: forall x . ctx -> eff x -> IO x }

data IOCtx (daa :: * -> *) = IOCtx
    { _ctxChgAccum :: ChgAccumCtx (IOCtx daa)
    , _ctxExec     :: BaseMIOExec daa (IOCtx daa)
    }

class HasGetter s a where
    {-# MINIMAL  gett #-}
    gett :: HasGetter s a => s -> a

instance HasGetter (IOCtx daa) (BaseMIOExec daa (IOCtx daa)) where
    gett = _ctxExec

type family ChgAccum ctx :: *
type instance ChgAccum (IOCtx (DbAccessM chgAccum id value)) = chgAccum

-- | Auxiliary datatype for context-dependant computations.
data ChgAccumCtx ctx = CAInitialized (ChgAccum ctx)

runERoCompIO :: forall da daa a .
    ( DbActions da daa (ChgAccum (IOCtx da)) IO
    )
    => daa IO
    -> ChgAccum (IOCtx da)
    -> BaseM da (IOCtx da) a
    -> IO a
runERoCompIO daa initChgAccum comp = runBaseMIO comp ctx
  where
    ctx :: IOCtx da
    ctx = IOCtx
      { _ctxChgAccum = CAInitialized initChgAccum
      , _ctxExec     = BaseMIOExec $ \(getCAOrDefault . _ctxChgAccum -> chgAccum) da -> executeEffect da daa chgAccum
      }

-- | Represented by sumChangeSetDaaM in blockchain-util in Snowdrop.Execution.DbActions.Simple (Simple.hs)
testDbaM :: DbAccessActionsM ChangeAccum Id Value IO
testDbaM = DbAccessActionsM
    { daaModifyAccum = liftA' modifyAccum
    }

    where
      liftA' f a b = pure $ f a b

      modifyAccum :: ChangeAccum -> [(Id, Value)] -> [ChangeAccum]
      modifyAccum chgAccum idVals = ChangeAccum idVals : [chgAccum]

-- | Implemented by modifyAccumOne or modifyAccum in Snowdrop.Core.ERoComp.Helpers (Helpers.hs)
-- | and used in BlkStateConfiguration as basic building block for monadic computations
baseMModifyAccum :: [(Id, Value)] -> BaseM (DbAccessM ChangeAccum Id Value) ctx Result
baseMModifyAccum idVals = effect (dbModifyAccum idVals)

dbModifyAccum :: [(Id, Value)] -> DbAccessM ChangeAccum Id Value Result
dbModifyAccum idVals = DbModifyAccum idVals (\chgAccum -> (Result chgAccum))

getCAOrDefault :: ChgAccumCtx ctx -> ChgAccum ctx
getCAOrDefault (CAInitialized cA) = cA

calculation :: [(Id, Value)] -> BaseM (DbAccessM ChangeAccum Id Value) ctx Result
calculation idVals = do
    result <- baseMModifyAccum idVals
    baseMModifyAccum $ incRes result

run :: IO Result
run = runERoCompIO testDbaM (ChangeAccum $ [(Id 0, Value '*')]) (calculation [(Id 1, Value 'A'), (Id 2, Value 'B'), (Id 3, Value 'C')])
