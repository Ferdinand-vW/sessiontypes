{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE RankNTypes                 #-}
-- | This module defines a GADT `STTerm` that is the very core of this library
--
-- Session typed programs are constructed by composing the constructors of `STTerm`.
--
-- Each constructor is annotated with a specific session type (except for `Ret` and `Lift`). 
--
-- By passing a constructor to another constructor as an argument their session types are joined
-- to form a larger session type.
--
-- We do not recommend explicitly composing the `STTerm` constructors. Instead make use of the functions defined in the "Control.SessionTypes.MonadSession" module.
--
-- Of course a `STTerm` program in itself is not very useful as it is devoid of any semantics.
-- However, an interpreter function can give meaning to a `STTerm` program. 
-- 
-- We define a couple in this library: "Control.SessionTypes.Debug", "Control.SessionTypes.Interactive", "Control.SessionTypes.Normalize" and "Control.SessionTypes.Visualize".
module Control.SessionTypes.STTerm (
  STTerm (..),
  inferIdentity
) where

import           Control.SessionTypes.MonadSession
import           Control.SessionTypes.Types
import qualified Control.SessionTypes.Indexed as I

import Control.Monad.IO.Class
import Data.Functor.Identity (Identity)
import Data.Kind
import Data.Typeable

-- | The STTerm GADT
--
-- Although we say that a `STTerm` is annotated with a session type, it is actually annotated with a capability (`Cap`).
-- 
-- The capability contains a context that is necessary for recursion and the session type.
--
-- The constructors can be split in four different categories:
--
--    * Communication: `Send` and `Recv` for basic communication
--    * Branching: `Sel1`, `Sel2`, `OffZ` and `OffS`
--    * Recursion: `Rec`, `Weaken` and `Var`
--    * Unsession typed: `Ret` and `Lift`
data STTerm :: forall a. (Type -> Type) -> Cap a -> Cap a -> Type -> Type where
  -- | The constructor for sending messages. It is annotated with the send session type (`:!>`).
  --
  -- It takes as an argument, the message to send, of type equal to the first argument of `:!>` and the continuing `STTerm` that is session typed with the second argument of `:!>`.
  Send :: a -> STTerm m ('Cap ctx r) r' b -> STTerm m ('Cap ctx (a :!> r)) r' b
  -- | The constructor for receiving messages. It is annotated with the receive session type (`:?>`)
  --
  -- It takes a continuation that promises to deliver a value that may be used in the rest of the program.
  Recv :: (a -> STTerm m ('Cap ctx r) r' b) -> STTerm m ('Cap ctx (a :?> r)) r' b
  -- | Selects the first branch in a selection session type.
  --
  -- By selecting a branch, that selected session type must then be implemented.
  Sel1 :: STTerm m ('Cap ctx s) r a -> STTerm m ('Cap ctx (Sel (s ': xs))) r a
  -- | Skips a branch in a selection session type.
  -- 
  -- If the first branch in the selection session type is not the one we want to implement
  -- then we may use `Sel2` to skip this.
  Sel2 :: STTerm m ('Cap ctx (Sel (t ': xs))) r a -> STTerm m ('Cap ctx (Sel (s ': t ': xs))) r a
  -- | Dually to selection there is also offering branches.
  --
  -- Unlike selection, where we may only implement one branch, an offering asks you to implement all branches. Which is chosen depends
  -- on how an interpreter synchronizes selection with offering.
  -- 
  -- This constructor denotes the very last branch that may be offered.
  OffZ :: STTerm m ('Cap ctx s) r a -> STTerm m ('Cap ctx (Off '[s])) r a
  -- | offers a branch and promises at least one more branch to be offered.
  OffS :: STTerm m ('Cap ctx s) r a -> STTerm m ('Cap ctx (Off (t ': xs))) r a -> STTerm m ('Cap ctx (Off (s ': t ': xs))) r a
  -- | Constructor for delimiting the scope of recursion
  --
  -- The recursion constructors also modify or at least make use of the context in the capability.
  --
  -- The `Rec` constructor inserts the session type argument to `R` into the context of the capability of its `STTerm` argument.
  --
  -- This is necessary such that we remember the session type of the body of code that we may want to recurse over and thus avoiding
  -- infinite type occurrence errors.
  Rec :: STTerm m ('Cap (s ': ctx) s) r a -> STTerm m ('Cap ctx (R s)) r a
  -- | Constructor for weakening (expanding) the scope of recusion
  -- 
  -- This constructor does the opposite of `R` by popping a session type from the context.
  --
  -- Use this constructor to essentially exit a recursion
  Weaken :: STTerm m ('Cap ctx t) r a -> STTerm m ('Cap (s ': ctx) (Wk t)) r a
  -- | Constructor that denotes the recursion variable
  --
  -- It assumes the context to be non-empty and uses the session type at the top of the context to determine what should be implemented after `Var`.
  Var :: STTerm m ('Cap (s ': ctx) s) t a -> STTerm m ('Cap (s ': ctx) V) t a
  -- | Constructor that makes `STTerm` a (indexed) monad
  Ret :: (a :: Type) -> STTerm m s s a
  -- | Constructor that makes `STTerm` a (indexed) monad transformer
  Lift :: m (STTerm m s r a) -> STTerm m s r a

deriving instance Typeable (STTerm m s r a)

instance Functor (STTerm m s s) where
  fmap f (Ret a) = Ret $ f a

instance Applicative (STTerm m s s) where
  pure x = Ret x
  (Ret f) <*> (Ret a) = Ret $ f a

instance Monad (STTerm m s s) where
  return = pure
  (Ret x) >>= f = f x

instance Monad m => I.IxFunctor (STTerm m) where
  fmap f st = st I.>>= \a -> I.return $ f a

instance Monad m => I.IxApplicative (STTerm m) where
  pure x = Ret x
  (<*>) = I.ap

instance Monad m => I.IxMonad (STTerm m) where
  return x = Ret x
  (Send a r) >>= f = Send a (r I.>>= f)
  (Recv x) >>= f = Recv $ \c -> x c I.>>= f
  (Sel1 s) >>= f = Sel1 $ s I.>>= f
  (Sel2 xs) >>= f = Sel2 $ xs I.>>= f 
  (OffZ s) >>= f = OffZ (s I.>>= f)
  (OffS s xs) >>= f = OffS (s I.>>= f) (xs I.>>= f)
  (Rec s) >>= f = Rec $ s I.>>= f
  (Var s) >>= f = Var $ s I.>>= f
  (Weaken s) >>= f = Weaken $ s I.>>= f
  (Lift m) >>= f = Lift $ do
    st <- m
    return $ st I.>>= f
  (Ret x) >>= f = f x

instance Monad m => I.IxMonadT (STTerm) m where
  lift m = Lift $ m >>= return . Ret

instance MonadIO m => I.IxMonadIO (STTerm m) where
  liftIO m = I.lift $ liftIO m 

instance Monad m => MonadSession (STTerm m) where
  send a = Send a (Ret ())
  recv = Recv Ret
  sel1 = Sel1 $ Ret ()
  sel2 = Sel2 $ Ret ()
  offZ = OffZ
  offS = OffS
  recurse = Rec
  weaken = Weaken
  var = Var
  eps = Ret

-- | This function can be used if we do not use `lift` in a program
-- but we must still disambiguate `m`.
inferIdentity :: STTerm Identity s r a -> STTerm Identity s r a
inferIdentity = id