-- | This packages provides a deep embedded domain-specific language for writing session typed program.
--
-- A session typed program is a program annotated with session types. A session type describes a communication protocol at the type-level.
-- 
-- The motivation for doing so is that it gives you a static guarantee that a program correctly implements a protocol. It may even guarantee that no deadlocking can occur.
--
-- The following constitutes the most important parts of this library for writing session typed programs.
--
-- * `STTerm`: A GADT representing the terms of the DSL. The constructors represent the different session types and are annotated with session types.
-- * `ST`: A protomoted data type describing the different session types.
-- * `MonadSession`: A type class exposing the interface of the DSL.
-- * "Control.SessionTypes.Indexed": A custom prelude module replacing common type classes with indexed type classes
--
-- This package also implements a couple interpreters that evaluate an abstract-syntax tree consisting of `STTerm` constructors:
--
-- * "Control.SessionTypes.Debug": Purely evaluation
-- * "Control.SessionTypes.Interactive": Interactive evaluation
-- * "Control.SessionTypes.Normalize": Rewrites `STTerm` programs to a normal form
-- * "Control.SessionTypes.Visualize": Visualizes a session type
module Control.SessionTypes (
  -- * STTerm
  STTerm (..),
  inferIdentity,
  -- * MonadSession
  -- ** Primitives
  MonadSession (..),
  -- ** Combinators
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
  eps0,
  -- * Types
  -- ** Session Types
  ST(..),
  Cap(..),
  GetST,
  GetCtx,
  -- ** Duality
  Dual,
  DualST,
  MapDual,
  -- ** Removing
  RemoveSend,
  RemoveSendST,
  MapRemoveSend,
  RemoveRecv,
  RemoveRecvST,
  MapRemoveRecv,
  -- ** Applying Constraints
  HasConstraint,
  HasConstraintST,
  MapHasConstraint,
  HasConstraints,
  -- ** Boolean functions
  IfThenElse,
  Not,
  Or,
  -- ** Product type
  Prod (..),
  Left,
  Right,
  -- ** Other
  Nat(..),
  Ref(..),
  TypeEqList,
  Append
) where

import Control.SessionTypes.STTerm (
  STTerm (..),
  inferIdentity
  )
import Control.SessionTypes.Types (
  ST(..),
  Cap(..),
  GetST,
  GetCtx,
  Dual,
  DualST,
  MapDual,
  RemoveSend,
  RemoveSendST,
  MapRemoveSend,
  RemoveRecv,
  RemoveRecvST,
  MapRemoveRecv,
  HasConstraint,
  HasConstraintST,
  MapHasConstraint,
  HasConstraints,
  IfThenElse,
  Not,
  Or,
  Prod (..),
  Left,
  Right,
  Nat(..),
  Ref(..),
  TypeEqList,
  Append
  )
import Control.SessionTypes.MonadSession (
  MonadSession (..),
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
  )