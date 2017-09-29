{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE FunctionalDependencies #-}
-- | This module provides a set of indexed type classes (IxFunctor, IxApplicative, IxMonad, etc..) that correspond to existing type classes (Functor, Applicative, Monad, etc..)
--
-- The intent of this module is to replace the use of non-indexed type classes with indexed type class.
-- 
-- For that reason the indexed type classes expose functions that are named the same as the functions exposed by a corresponding non-indexed type class.
--
-- There are two ways to use this module:
--
-- @
-- import           SessionTypes
-- import qualified SessionTypes.Indexed as I
--
-- prog = send 5 I.>> eps0
-- @
--
-- @
-- {-\# LANGUAGE RebindableSyntax \#-}
-- import SessionTypes
-- import SessionTypes.Indexed
-- 
-- prog = do
--  send 5
--  eps0
-- @
--
-- With `RebindableSyntax` we construct a custom do notation by rebinding (>>=) with (>>=) of `IxMonad`.
-- Rebinding is not limited to only (>>=), but also all other functions in Prelude. 
--
-- We do not want to force importing Prelude if you use `RebindableSyntax`. 
-- Therefore this module also exports Prelude that hides functions already defined by
-- the indexed type classes.
module Control.SessionTypes.Indexed (
  -- * Classes
  IxFunctor(..),
  IxApplicative(..),
  IxMonad(..),
  -- ** Transformers
  IxMonadT(..),
  IxMonadIxT(..),
  -- ** Mtl
  IxMonadReader(..),
  -- ** Exception
  IxMonadThrow(..),
  IxMonadCatch(..),
  IxMonadMask(..),
  -- ** MonadIO
  IxMonadIO(..),
  -- * Combinators
  ap,
  -- * Rebind
  ifThenElse,
  module PH,
) where

import Control.Exception
import Data.Kind (Type)
import Prelude as PH hiding ((>>=),(>>), return, fail, fmap, pure, (<*>))

class IxFunctor (f :: p -> p -> Type -> Type) where
  fmap :: (a -> b) -> f j k a -> f j k b

class IxFunctor f => IxApplicative (f :: p -> p -> Type -> Type) where
  pure :: a -> f i i a
  (<*>) :: f s r (a -> b) -> f r k a -> f s k b

infixl 1 >>=
infixl 1 >>

class IxApplicative m => IxMonad (m :: p -> p -> Type -> Type) where
  (>>=) :: m s t a -> (a -> m t k b) -> m s k b
  (>>) ::  m s t a -> m t k b -> m s k b
  return :: a -> m i i a
  fail ::  String -> m i i a
  m1 >> m2 = m1 >>= \_ -> m2
  fail = error

-- | Type class for lifting monadic computations
class IxMonad (t m) => IxMonadT t m where
  lift :: m a -> t m s s a

-- | Type class for lifting indexed monadic computations
class IxMonad (t m) => IxMonadIxT t m where
  ilift :: m s r a -> t m s r a

-- | Type class representing the indexed monad reader
class IxMonad m => IxMonadReader r m | m -> r where
  ask :: m s s r
  local :: (r -> r) -> m s t a -> m s t a
  reader :: (r -> a) -> m i i a

-- | Type class for indexed monads in which exceptions may be thrown.
class IxMonad m => IxMonadThrow m s where
  -- | Provide an `Exception` to be thrown
  throwM :: Exception e => e -> m s s a

-- | Type class for indexed monads to allow catching of exceptions.
class IxMonadThrow m s => IxMonadCatch m s where
  -- | Provide a handler to catch exceptions.
  catch :: Exception e => m s s a -> (e -> m s s a) -> m s s a

-- | Type class for indexed monads that may mask asynchronous exceptions.
class IxMonadCatch m s => IxMonadMask m s where
  -- | run an action that disables asynchronous exceptions. The provided function can be used to restore the occurrence of asynchronous exceptions.
  mask :: ((m s s b -> m s s b) -> m s s b) -> m s s b
  -- | Ensures that even interruptible functions may not raise asynchronous exceptions.
  uninterruptibleMask :: ((m s s b -> m s s b) -> m s s b) -> m s s b

-- | Type class for indexed monads that may lift IO computations.
class IxMonadIO m where
  liftIO :: IO a -> m s s a

ifThenElse :: Bool -> t -> t -> t
ifThenElse True b1 _ = b1
ifThenElse False _ b2 = b2

-- # Combinators

ap :: IxMonad m => m s r (a -> b) -> m r k a -> m s k b
ap f g = f >>= \f' -> g >>= \g' -> return (f' g')