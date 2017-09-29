{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | This module provides an interface for writing session typed programs
module SessionTypes.MonadSession (
  -- * Primitives
  MonadSession (..),
  -- * Combinators
  empty,
  empty0,
  selN,
  selN1,
  selN2,
  selN3,
  selN4,
  Select(sel),
  (<&),
  (<&>),
  offer,
  recurseFix,
  recurse0,
  weaken0,
  var0,
  eps0
) where

import SessionTypes.Indexed as I
import SessionTypes.Types

import Data.Function (fix)
import Data.Typeable (Proxy(..))

-- | The `MonadSession` type class exposes a set of functions that composed together form a session typed program
-- 
-- A type that is an instance of `MonadSession` must therefore also be an instance of `IxMonad`.
--
-- The functions themselves are generally defined as wrappers over corresponding `STTerm` constructors.
class IxMonad m => MonadSession m where
  send :: a -> m ('Cap ctx (a :!> r))            ('Cap ctx r) ()
  recv ::      m ('Cap ctx (a :?> r))            ('Cap ctx r) a
  sel1 ::      m ('Cap ctx (Sel (s ': xs)))      ('Cap ctx s) ()
  sel2 ::      m ('Cap ctx (Sel (s ': t ': xs))) ('Cap ctx (Sel (t ': xs))) ()
  offZ ::      m ('Cap ctx s) r a ->        m ('Cap ctx (Off '[s])) r a
  offS ::      m ('Cap ctx s) r a ->        m ('Cap ctx (Off (t ': xs))) r a -> m ('Cap ctx (Off (s ': t ': xs))) r a
  recurse ::   m ('Cap (s ': ctx) s) r a -> m ('Cap ctx (R s)) r a
  weaken ::    m ('Cap ctx s) r a ->        m ('Cap (t ': ctx) (Wk s)) r a
  var ::       m ('Cap (s ': ctx) s) r a -> m ('Cap (s ': ctx) V) r a
  eps ::  a -> m ('Cap ctx Eps) ('Cap ctx Eps) a

-- | A session typed program that is polymorphic in its context can often not be used by interpreters.
--
-- We can apply `empty` to the session typed program before passing it to an interpreter to instantiate that the context is empty.
empty :: MonadSession m => m ('Cap '[] s) r a -> m ('Cap '[] s) r a
empty = id

-- | Monadic composable definition of `empty`
--
-- Prefix a session typed program with (empty >>) to instantiate the context to be empty.
empty0 :: MonadSession m => m ('Cap '[] r) ('Cap '[] r) ()
empty0 = I.return ()

-- | Allows indexing of selections.
--
-- The given `Ref` type can be used as an indexed to select a branch. This circumvents the need to sequence a bunch of `sel1` and `sel2` to select a branch.
--
-- @
-- prog :: MonadSession m => m ('Cap ctx (Sel '[a,b,c,d])) ('Cap ctx Eps) ()
--
-- MonadSession m => m ('Cap ctx b) ('Cap ctx Eps) ()
-- prog2 = prog >> selN (RefS RefZ)
-- @
--
selN :: MonadSession m => Ref s xs -> m ('Cap ctx (Sel xs)) ('Cap ctx s) ()
selN RefZ = sel1
selN (RefS r) = sel2 I.>> selN r

-- | Select the first branch of a selection.
selN1 :: MonadSession m => m ('Cap ctx (Sel (s ': xs))) ('Cap ctx s) ()
selN1 = sel1

-- | Select the second branch of a selection.
selN2 :: MonadSession m => m ('Cap ctx (Sel (s ': t ': xs))) ('Cap ctx t) ()
selN2 = sel2 I.>> sel1

-- | Select the third branch of a selection.
selN3 :: MonadSession m => m ('Cap ctx (Sel (s ': t ': k ': xs))) ('Cap ctx k) ()
selN3 = sel2 I.>> sel2 I.>> sel1

-- | Select the fourth branch of a selection.
selN4 :: MonadSession m => m ('Cap ctx (Sel (s ': t ': k ': r ': xs))) ('Cap ctx r) ()
selN4 = sel2 I.>> sel2 I.>> sel2 I.>> sel1

-- | Type class for selecting a branch through injection.
--
-- Selects the first branch that matches the given session type.
--
-- @
-- prog :: MonadSession m => m ('Cap ctx (Sel '[Eps, String :!> Eps, Int :!> Eps])) ('Cap ctx Eps) ()
-- prog = sel >> send "c" >>= eps
-- @
--
-- It should be obvious that you cannot select a branch using `sel` if that branch has the same session type as a previous branch.
class Select xs s where
  sel :: MonadSession m => m ('Cap ctx (Sel xs)) ('Cap ctx s) ()

instance (tl ~ TypeEqList xs s, Select' xs s tl) => Select xs s where
  sel = sel' (Proxy :: Proxy tl)

class Select' xs s (tl :: k) | xs tl -> s where
  sel' :: MonadSession m => Proxy tl -> m ('Cap ctx (Sel xs)) ('Cap ctx s) ()

instance Select' (s ': xs) s ('True ': tl) where
  sel' _ = sel1

instance Select' (r ': xs) t tl => Select' (s ': r ': xs) t ('False ': tl) where
  sel' _ = sel2 I.>> sel' (Proxy :: Proxy tl)

-- | Takes two session typed programs and constructs an offering consisting of two branches
offer :: MonadSession m => m ('Cap ctx s) r a -> m ('Cap ctx t) r a -> m ('Cap ctx (Off '[s, t])) r a
offer s r = offS s (offZ r)

-- | Infix synonym for `offS`
infixr 1 <&
(<&) :: MonadSession m => m ('Cap ctx s) r a -> m ('Cap ctx (Off (t ': xs))) r a -> m ('Cap ctx (Off (s ': t ': xs))) r a
(<&) = offS

-- | Infix synonym for `offer`
-- 
-- Using both `<&` and `<&>` we can now construct an offering as follows:
--
-- @
--  branch1 
--  \<& branch2
--  \<& branch3
--  \<&\> branch4
-- @
--
-- This will be parsed as
--
-- @
-- (branch1
--  \<& (branch2
--  \<& (branch3
--  \<&\> branch4)))
-- @
infix 2 <&>
(<&>) :: MonadSession m => m ('Cap ctx s) r a -> m ('Cap ctx t) r a -> m ('Cap ctx (Off '[s, t])) r a
s <&> r = offS s (offZ r)

-- | A fixpoint combinator for recursion
-- 
-- The argument function must take a recursion variable as an argument that can be used to denote the point of recursion.
--
-- For example:
--
-- @
-- prog = recurseFix \\f -> do
--  send 5
--  f
-- @
--
-- This program will send the number 5 an infinite amount of times.
recurseFix :: MonadSession m => (m ('Cap (s ': ctx) V) r a -> m ('Cap (s ': ctx) s) r a) -> m ('Cap ctx (R s)) r a
recurseFix s = recurse $ fix (\f -> s $ var f)

-- | Monadic composable definition of `recurse`
recurse0 :: MonadSession m => m ('Cap ctx (R s)) ('Cap (s ': ctx) s) ()
recurse0 = recurse $ I.return ()

-- | Monadic composable definition of `weaken`
weaken0 :: MonadSession m => m ('Cap (t ': ctx) (Wk s)) ('Cap ctx s) ()
weaken0 = weaken $ I.return ()

-- | Monadic composable definition of `var`
var0 :: MonadSession m => m ('Cap (s ': ctx) V) ('Cap (s ': ctx) s) ()
var0 = var $ I.return ()

-- | Monadic composable definition of `eps`
eps0 :: MonadSession m => m ('Cap ctx Eps) ('Cap ctx Eps) ()
eps0 = eps ()