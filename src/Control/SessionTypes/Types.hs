{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
-- | This module provides a collection of types and type families.
--
-- Specifically it defines the session type data type, capability data type and type families that compute using session types or capabilities as arguments.
module Control.SessionTypes.Types (
  -- * Session Types
  ST(..),
  Cap(..),
  GetST,
  GetCtx,
  -- * Duality
  Dual,
  DualST,
  MapDual,
  -- * Removing
  RemoveSend,
  RemoveSendST,
  MapRemoveSend,
  RemoveRecv,
  RemoveRecvST,
  MapRemoveRecv,
  -- * Applying Constraints
  HasConstraint,
  HasConstraintST,
  MapHasConstraint,
  HasConstraints,
  -- * Boolean functions
  IfThenElse,
  Not,
  Or,
  -- * Product type
  Prod (..),
  Left,
  Right,
  -- * Other
  Nat(..),
  Ref(..),
  TypeEqList,
  Append
) where

import Data.Kind
import Data.Typeable

infixr 6 :?>
infixr 6 :!>

-- | The session type data type
--
-- Each constructor denotes a specific session type. Using the `DataKinds` pragma the constructors are promoted to types and `ST` is promoted to a kind.
data ST a = (:?>) a (ST a) -- ^ Send a value
    | (:!>) a (ST a) -- ^ Recv a value
    | Sel [ST a] -- ^ Selection of branches
    | Off [ST a] -- ^ Offering of branches
    | R (ST a)  -- ^ Delimit the scope of recursion
    | Wk (ST a) -- ^ Weaken the scope of recursion
    | V -- ^ Recursion variable
    | Eps -- ^ End of the session
    deriving Typeable

-- | A capability that stores a context/scope that is a list of session types and a session type
data Cap a = Cap [ST a] (ST a) deriving Typeable

-- | Retrieves the session type from the capability
type family GetST s where
  GetST ('Cap ctx s) = s

-- | Retrieves the context from the capability
type family GetCtx s where
  GetCtx ('Cap ctx s) = ctx

-- | Type family for calculating the dual of a session type. It may be applied to a capability.
-- 
-- We made `Dual` injective to support calculating the dual of a selection that contains
-- an ambiguous branch. Of course that does require that the dual of that ambiguous branch must be known.
type family Dual s = r | r -> s where
  Dual ('Cap ctx s) = 'Cap (MapDual ctx) (DualST s)

-- | Type family for calculating the dual of a session type. It may be applied to the actual session type.
type family DualST (a :: ST c) = (b :: ST c) | b -> a where
  DualST (s :!> r) = s :?> DualST r
  DualST (s :?> r) = s :!> DualST r
  DualST (Sel xs)  = Off (MapDual xs)
  DualST (Off xs)  = Sel (MapDual xs)
  DualST (R s)     = R (DualST s)
  DualST (Wk s)    = Wk (DualST s)
  DualST V         = V
  DualST Eps       = Eps

-- | Type family for calculating the dual of a list of session types.
type family MapDual xs = ys | ys -> xs where
  MapDual '[] = '[]
  MapDual (s ': xs) = DualST s ': MapDual xs

-- | Type family for removing the send session type from the given session type. It may be applied to a capability.
type family RemoveSend s where
  RemoveSend ('Cap ctx s) = 'Cap (MapRemoveSend ctx) (RemoveSendST s)

-- | Type family for removing the send session type from the given session type. It may be applied to a session type.
type family RemoveSendST s where
  RemoveSendST (a :!> r) = RemoveSendST r
  RemoveSendST (a :?> r) = a :?> RemoveSendST r
  RemoveSendST (Sel xs) = Sel (MapRemoveSend xs)
  RemoveSendST (Off xs) = Off (MapRemoveSend xs)
  RemoveSendST (R s) = R (RemoveSendST s)
  RemoveSendST (Wk s) = Wk (RemoveSendST s)
  RemoveSendST s = s

-- | Type family for removing the send session type from a list of session types.
type family MapRemoveSend ctx where
  MapRemoveSend '[] = '[]
  MapRemoveSend (s ': ctx) = RemoveSendST s ': MapRemoveSend ctx

-- | Type family for removing the receive session type from the given session type. It may be applied to a capability.
type family RemoveRecv s where
  RemoveRecv ('Cap ctx s) = 'Cap (MapRemoveRecv ctx) (RemoveRecvST s)

-- | Type family for removing the receive session type from the given session type. It may be applied to a session type.
type family MapRemoveRecv ctx where
  MapRemoveRecv '[] = '[]
  MapRemoveRecv (s ': ctx) = RemoveRecvST s ': MapRemoveRecv ctx

-- | Type family for removing the receive session type from a list of session types.
type family RemoveRecvST s where
  RemoveRecvST (a :!> r) = a :!> RemoveRecvST r
  RemoveRecvST (a :?> r) = RemoveRecvST r
  RemoveRecvST (Sel xs) = Sel (MapRemoveRecv xs)
  RemoveRecvST (Off xs) = Off (MapRemoveRecv xs)
  RemoveRecvST (R s) = R (RemoveRecvST s)
  RemoveRecvST (Wk s) = Wk (RemoveRecvST s)
  RemoveRecvST s = s

-- | Type family for applying a constraint to types of kind `Type` in a session type. It may be applied to a capability.
type family HasConstraint (c :: Type -> Constraint) s :: Constraint where
  HasConstraint c ('Cap ctx s) = (HasConstraintST c s, MapHasConstraint c ctx)

-- | Type family for applying a constraint to types of kind `Type` in a session type. It may be applied to a session type.
type family MapHasConstraint (c :: Type -> Constraint) ss :: Constraint where
  MapHasConstraint c '[] = ()
  MapHasConstraint c (s ': ss) = (HasConstraintST c s, MapHasConstraint c ss)

-- | Type family for applying a constraint to types of kind `Type` in a list of session types.
type family HasConstraintST (c :: Type -> Constraint) s :: Constraint where
  HasConstraintST c (a :!> r) = (c a, HasConstraintST c r)
  HasConstraintST c (a :?> r) = (c a, HasConstraintST c r)
  HasConstraintST c (Sel '[]) = ()
  HasConstraintST c (Sel (s ': xs)) = (HasConstraintST c s, HasConstraintST c (Sel xs))
  HasConstraintST c (Off '[]) = ()
  HasConstraintST c (Off (s ': xs)) = (HasConstraintST c s, HasConstraintST c (Off xs))
  HasConstraintST c (R s) = HasConstraintST c s
  HasConstraintST c (Wk s) = HasConstraintST c s
  HasConstraintST c V = ()
  HasConstraintST c s = ()

-- | Type family for applying zero or more constraints to types of kind `Type` in a list of session types. It may be applied to a capability.
type family HasConstraints (cs :: [Type -> Constraint]) s :: Constraint where
  HasConstraints '[] s = ()
  HasConstraints (c ': cs) s = (HasConstraint c s, HasConstraints cs s)

-- | Type family for applying zero or more constraints to types of kind `Type` in a list of session types. It may be applied to a session type.
type family HasConstraintsST (cs :: [Type -> Constraint]) s :: Constraint where
  HasConstraintsST '[] s = ()
  HasConstraintsST (c ': cs) s = (HasConstraintST c s, HasConstraintsST cs s)

-- | Type family for applying zero or more constraints to types of kind `Type` in a list of session types. It may be applied to a list of session types.
type family MapHasConstraints (cs :: [Type -> Constraint]) ctx :: Constraint where
  MapHasConstraints '[] ctx = ()
  MapHasConstraints (c ': cs) ctx = (MapHasConstraint c ctx, MapHasConstraints cs ctx)

-- | Promoted `ifThenElse`
type family IfThenElse (b :: Bool) (l :: k) (r :: k) :: k where
  IfThenElse 'True l r = l
  IfThenElse 'False l r = r 

-- | Promoted `not`
type family Not b :: Bool where
  Not 'True  = 'False
  Not 'False = 'True

-- | Promoted `||`
type family Or b1 b2 :: Bool where
  Or 'True b = 'True
  Or b 'True = 'True
  Or b1 b2 = 'False

-- | Data type that takes a kind as an argument. Its sole constructor takes two capabilities parameterized by the kind argument.
--
-- This data type is useful if it is necessary for an indexed monad to be indexed by four parameters. 
data Prod t = (:*:) (Cap t) (Cap t)

-- | Type family for returning the first argument of a product.
type family Left p where
  Left (l :*: r) = l

-- | Type family for returning the second argument of a product.
type family Right p where
  Right (l :*: r) = r

-- | Data type defining natural numbers
data Nat = Z | S Nat deriving (Show, Eq, Ord)

-- | Data type that can give us proof of membership of an element in a list of elements.
data Ref s xs where
  RefZ :: Ref s (s ': xs)
  RefS :: Ref s (k ': xs) -> Ref s (t ': k ': xs)

-- | Type family for computing which types in a list of types are equal to a given type.
type family TypeEqList xs s where
  TypeEqList '[s] s = '[True]
  TypeEqList '[r] s = '[False]
  TypeEqList (s ': xs) s = 'True ': TypeEqList xs s
  TypeEqList (r ': xs) s = 'False ': TypeEqList xs s

-- | Promoted `++`
type family Append xs ys where
  Append '[] ys = ys
  Append (x ': xs) ys = x ': xs `Append` ys 