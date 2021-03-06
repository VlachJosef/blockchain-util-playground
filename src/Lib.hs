{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module Lib where

import           Control.Monad.State.Class      (MonadState, gets, modify)
import           Control.Monad.Trans.State.Lazy (StateT, runStateT)

import           Control.Monad                  (join)
import           Control.Monad.Reader           (ReaderT (..), ask, asks, local)
import           Control.Monad.Reader.Class     (MonadReader)
import           Control.Monad.Trans.Class      (lift)
import           Data.Char                      (chr)
import           Data.Foldable                  (foldMap)
import           Data.Function                  ((&))
import           Data.Functor                   (Functor)
import           Lens.Micro                     (Lens, lens, (.~))

newtype Id = Id Int deriving Show
newtype Value = Value Char deriving Show
newtype Result = Result [ChangeAccum] deriving Show
newtype ChangeAccum = ChangeAccum
    { unChangeAccum :: [(Id, Value)]
    } deriving Show

-- | Auxiliary function for testing of baseMModifyAccum
-- | Increment Id by one (I bet there is lens one-liner for this)
incRes :: [ChangeAccum] -> [(Id, Value)]
incRes res = join (incIds <$> (unChangeAccum <$> res))
  where
    incIds :: [(Id, Value)] -> [(Id, Value)]
    incIds xs = incId <$> xs

    incId :: (Id, Value) -> (Id, Value)
    incId (Id i, value) = (Id (i+1), value)

-- | Core follows | --

data DbAccess id value res = DbQuery id (value -> res)

data DbAccessM chgAccum id value res
    = DbModifyAccum [(id, value)] ([chgAccum] -> res)
    | DbAccess (DbAccess id value res)

data DbAccessActions chgAccum id value m = DbAccessActions
    { daaGetter :: chgAccum -> id -> m value
    }

data DbAccessActionsM chgAccum id value m = DbAccessActionsM
    { daaAccess      :: DbAccessActions chgAccum id value m
    , daaModifyAccum :: chgAccum -> [(id, value)] -> m [chgAccum]
    }

class DbActions (effect :: * -> *) (actions :: (* -> *) -> *) param (m :: * -> *) where
    -- | Execute @effect r@ using @actions m@ and return value @r@ in monad @m@.
    executeEffect :: effect r -> actions m -> param -> m r

instance Functor m => DbActions (DbAccess p r)
                                (DbAccessActions chgAccum p r) chgAccum m where
    executeEffect (DbQuery p cont) daa chgAccum = cont <$> daaGetter daa chgAccum p

instance Functor m => DbActions (DbAccessM chgAccum id value)
                                (DbAccessActionsM chgAccum id value) chgAccum m where
    executeEffect (DbAccess da) (daaAccess -> daa) chgAccum = executeEffect da daa chgAccum
    executeEffect (DbModifyAccum chgSet cont) daaM chgAccum =
        cont <$> daaModifyAccum daaM chgAccum chgSet

class Monad m => Effectful eff m where
    -- | Executes effect `eff` in monad `m`.
    -- A natural transformation from effect data type to monad.
    effect :: eff a -> m a

type BaseMConstraint eff ctx m = ( Effectful eff m
                                 , MonadReader ctx m
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
deriving instance MonadReader ctx (BaseMIO eff ctx)

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

class HasGetter s a => HasLens s a where
    {-# MINIMAL lensFor | sett #-}

    sett :: HasLens s a => s -> a -> s
    sett s b = s & (lensFor @s @a) .~ b

    lensFor :: HasLens s a => Lens s s a a
    lensFor = lens gett (sett @s @a)

instance HasGetter (IOCtx daa) (BaseMIOExec daa (IOCtx daa)) where
    gett = _ctxExec

type family ChgAccum ctx :: *
type instance ChgAccum (IOCtx (DbAccessM chgAccum id value)) = chgAccum

-- | Auxiliary datatype for context-dependant computations.
data ChgAccumCtx ctx = CAInitialized (ChgAccum ctx) | CANotInitialized

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

runERwCompIO
  :: forall da daa s ctx a .
    ( DbActions da daa (ChgAccum (IOCtx da)) IO
    )
    => daa IO
    -> s
    -> ERwComp da (IOCtx da) s a
    -> IO (a, s)
runERwCompIO daa initS comp = runBaseMIO (runERwComp comp initS) $
        IOCtx
          { _ctxChgAccum = CANotInitialized
          , _ctxExec = BaseMIOExec $ \(getCAOrDefault . _ctxChgAccum -> chgAccum) da -> executeEffect da daa chgAccum
          }

-- | StateT over ERoComp.
-- ERoComp can be lifted to ERwComp with regarding a current state.
newtype ERwComp eff ctx s a = ERwComp { unERwComp :: StateT s (BaseM eff ctx) a }
    deriving (Functor, Applicative, Monad, MonadState s)

-- | Run a ERwComp with a passed initial state.
runERwComp
  :: forall eff ctx s a.
    ( HasGetter ctx (ChgAccumCtx ctx)
    )
  => ERwComp eff ctx s a
  -> s
  -> BaseM eff ctx (a, s)
runERwComp stComp initS = do
    mChgAccum <- asks (gett @_ @(ChgAccumCtx ctx))
    case mChgAccum of
        CANotInitialized -> pure ()
        CAInitialized _  -> error "throwLocalError ChgAccumCtxUnexpectedlyInitialized"
    runStateT (unERwComp stComp) initS


-- | Lift passed ERoComp to ERwComp.
-- Set initial state of ERoComp as ChgAccum from state from ERwComp.
liftERoComp
    :: forall eff2 ctx s eff1 a.
    ( HasLens ctx (ChgAccumCtx ctx)
    , HasGetter s (ChgAccum ctx)
    , ConvertEffect ctx eff1 eff2
    )
    => BaseM eff1 ctx a
    -> ERwComp eff2 ctx s a
liftERoComp comp =
    gets (gett @_ @(ChgAccum ctx)) >>= ERwComp . lift . flip initAccumCtx (convertEffect comp)

-- | Runs computation with specified initial Change Accumulator.
initAccumCtx
    :: forall eff ctx a .
    ( HasLens ctx (ChgAccumCtx ctx)
    )
    => ChgAccum ctx
    -> BaseM eff ctx a
    -> BaseM eff ctx a
initAccumCtx acc' comp = do
    gett @_ @(ChgAccumCtx ctx) <$> ask >>= \case
        CAInitialized _ -> error "ChgAccumCtxUnexpectedlyInitialized"
        CANotInitialized ->
            local (lensFor @ctx @(ChgAccumCtx ctx) .~ CAInitialized @ctx acc' ) comp

instance MonadReader ctx (BaseM eff ctx) where
    local f a = BaseM $ local (f :: ctx -> ctx) $ unBaseM a
    ask = BaseM ask

testDba :: DbAccessActions ChangeAccum Id Value IO
testDba = DbAccessActions
  { daaGetter = \chgAccum (Id id) -> pure (Value $ chr id)
  }

-- | Represented by sumChangeSetDaaM in blockchain-util in Snowdrop.Execution.DbActions.Simple (Simple.hs)
testDbaM :: DbAccessActionsM ChangeAccum Id Value IO
testDbaM = DbAccessActionsM
    { daaAccess = testDba
    , daaModifyAccum = liftA' modifyAccum
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

baseMQuery :: BaseM (DbAccess Id Value) ctx Result
baseMQuery = effect dbQuery

dbQuery :: DbAccess Id Value Result
dbQuery  = DbQuery (Id 42) (\chgAccum -> (Result [ChangeAccum [(Id 111, chgAccum)]]))

getCAOrDefault :: ChgAccumCtx ctx -> ChgAccum ctx
getCAOrDefault (CAInitialized cA) = cA
getCAOrDefault CANotInitialized   = error "getCAOrDefault CANotInitialized"

calculation :: [(Id, Value)] -> BaseM (DbAccessM ChangeAccum Id Value) (IOCtx (DbAccessM ChangeAccum Id Value)) Result
calculation idVals = do
    (Result res1) <- convertEffect baseMQuery
    (Result res2) <- baseMModifyAccum idVals
    baseMModifyAccum $ ((incRes res2) ++ (join (unChangeAccum <$> res1)))

calculationW :: ERwComp (DbAccessM ChangeAccum Id Value) (IOCtx (DbAccessM ChangeAccum Id Value)) ChangeAccum Result
calculationW = do
    chgSet :: Result <- liftERoComp baseMQuery
    modify . flip sett $ chgSet
    pure chgSet

instance HasGetter ChangeAccum Result where
    gett ca = Result [ca]

instance HasLens ChangeAccum Result where
    sett (ChangeAccum ca) (Result chgAccs) = ChangeAccum (foldMap unChangeAccum chgAccs ++ ca)

instance HasLens (IOCtx daa) (ChgAccumCtx (IOCtx daa)) where
    sett ctx val = ctx { _ctxChgAccum = val }

instance HasGetter ChangeAccum ChangeAccum where
  gett = id

instance HasGetter (IOCtx daa) (ChgAccumCtx (IOCtx daa)) where
  gett = _ctxChgAccum

run :: IO Result
run = runERoCompIO testDbaM (ChangeAccum $ [(Id 0, Value 'I')]) (calculation [(Id 1, Value 'A'), (Id 2, Value 'B'), (Id 3, Value 'C')])

runw :: IO (Result, ChangeAccum)
runw = runERwCompIO testDbaM (ChangeAccum $ [(Id 0, Value 'I')]) calculationW

class ConvertEffect ctx eff1 eff2 where
    convertEffect :: BaseM eff1 ctx a -> BaseM eff2 ctx a

newtype DbAccessT (eff1 :: * -> * -> * -> *) (eff2 :: * -> * -> * -> *) m a = DbAccessT { runDbAccessT :: m a }
    deriving (Functor, Applicative, Monad, MonadReader ctx)

instance (Effectful (DbAccessM chgAccum id value) m)
    => Effectful (DbAccess id value)
                 (DbAccessT DbAccess (DbAccessM chgAccum) m) where
    effect da = DbAccessT $ effect (DbAccess @chgAccum da)

instance ConvertEffect ctx (DbAccess id value) (DbAccessM chgAccum id value) where
    convertEffect (BaseM action) = BaseM ( runDbAccessT @DbAccess @(DbAccessM chgAccum) action )
