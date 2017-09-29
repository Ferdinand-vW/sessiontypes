{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RebindableSyntax #-}
-- | This module defines a new type for constructing more efficient `STTerm` programs.
module SessionTypes.Codensity where

import SessionTypes.STTerm
import SessionTypes.MonadSession
import SessionTypes.Indexed hiding (abs)

-- | We define an indexed codensity monad that allows us to reduce quadratic complexity
-- from repeated use of (>>=) in a session typed program to linear complexity.
newtype IxC m s r a = IxC { runIxC :: forall b k. (a -> STTerm m r k b) -> STTerm m s k b }

instance IxFunctor (IxC m) where
  fmap f (IxC x) = IxC $ \c -> x (c . f)

instance IxApplicative (IxC m) where
  pure = return
  (<*>) = ap

instance IxMonad (IxC m) where
  return a = IxC $ \h -> h a
  (IxC h) >>= f = IxC $ \c -> h $ \a -> runIxC (f a) c

instance Monad m => MonadSession (IxC m) where
  send a = IxC $ \h -> send a >>= h
  recv = IxC $ \h -> recv >>= h
  sel1 = IxC $ \h -> sel1 >>= h
  sel2 = IxC $ \h -> sel2 >>= h
  offZ (IxC f) = IxC $ \h -> offZ (f h)
  offS (IxC f) (IxC g) = IxC $ \h -> offS (f h) (g h) 
  recurse (IxC f) = IxC $ \h -> recurse $ f h
  weaken (IxC f) = IxC $ \h -> weaken $ f h 
  var (IxC f) = IxC $ \h -> var $ f h
  eps a = IxC $ \h -> h a

-- | Turns the `IxC` representation of a program to the `STTerm` representation.
--
-- The idea is to apply `abs` on a `IxC` program to make the resulting `STTerm` program more efficient.
abs :: Monad m => IxC m s r a -> STTerm m s r a
abs (IxC f) = f $ \a -> return a

-- | Transforms an `STTerm` program into a `IxC` representation.
-- 
-- Note that applying this function to a session typed program and then
-- applying `abs` to the result will not be more efficient.
--
-- This is because applying `rep` already induces quadratic complexity.
rep :: Monad m => STTerm m s r a -> IxC m s r a
rep m = IxC $ \h -> m >>= h
