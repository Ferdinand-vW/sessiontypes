{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE UndecidableInstances   #-}
-- | This module describes an interpreter for purely evaluating session typed programs
--
-- that is based on the paper /Beauty in the beast/ by /Swierstra, W., & Altenkirch, T./
--
-- Impurity in a session typed programs mainly comes from three things: receives, branching and lifting.
--
-- Using the session type we can easily determine the type of the message that each receive should expect.
--
-- This information allows us to define a stream of values of different types that provides input for each receive.
--
-- In the sessiontyped-distributed library we send and receive booleans to enable branching. 
-- 
-- It is also possible to provide some kind of input that makes this choice.
--
-- The current structure of the `Lift` constructor does not allow us to purely evaluate a `Lift`.
--
-- As such a session typed program may not contain a lift for it to be purely evaluated. See `runM` as an alternative.
module Control.SessionTypes.Debug (
  -- * Pure
  run,
  runAll,
  runSingle,
  runM,
  runAllM,
  runSingleM,
  -- * Input
  Stream(..),
  -- * Output
  Output(..)
) where

import           Control.SessionTypes
import qualified Control.SessionTypes.Indexed as I

import Control.DeepSeq (NFData, rnf)
import Data.Kind (Type)



-- | Purely evaluates a given `STTerm` using the input defined by `Stream`.
-- 
--   The output is described in terms of the session type actions within the given program
--
-- An example of how to use this function goes as follows:
--
-- @
--  prog :: STTerm Identity ('Cap '[] (Int :!> String :?> Eps)) ('Cap '[] Eps) String
--  prog = send 5 >> recv >>= eps
--
--  strm = S_Send $ S_Recv "foo" S_Eps
-- @
--
-- >>> run prog strm
-- O_Send 5 $ O_Recv "foo" $ O_Eps "foo"
run :: HasConstraint Show s => STTerm m s ('Cap ctx 'Eps) a -> Stream s -> Output s a
run st inp = (run' $ st) inp

-- | Instead of describing the session typed actions, it returns a list of the results
-- of all branches of all offerings.
--
-- @
-- prog = offer (eps 10) (eps 5)
-- strm = S_OffS S_Eps S_Eps
-- @
--
-- >>> runAll prog strm
-- [10,5]
runAll :: HasConstraint Show s => STTerm m s ('Cap ctx 'Eps) a -> Stream s -> [a]
runAll st stm = evalOutput $ run st stm

-- | Same as `runAll` but applies `head` to the resulting list
--
-- >>> runSingle prog strm
-- 10
runSingle :: HasConstraint Show s => STTerm m s ('Cap ctx 'Eps) a -> Stream s -> a
runSingle st stm = head $ evalOutput $ run st stm 

run' :: (HasConstraint Show s) => STTerm m s r a -> Stream s -> Output s a
run' (Send a r) (S_Send s_r) = O_Send a $ run' r s_r
run' (Recv c) (S_Recv a s_r) = O_Recv a $ run' (c a) s_r
run' (Sel1 s) (S_Sel1 s_s) = O_Sel1 $ run' s s_s
run' (Sel2 r) (S_Sel2 s_r) = O_Sel2 $ run' r s_r
run' (OffZ s) (S_OffZ s_s) = O_OffZ $ run' s s_s
run' (OffS s r) (S_OffS s_s s_r) = O_OffS (run' s s_s) (run' r s_r)
run' (OffZ s) (S_Off1 s_s) = O_Off1 $ run' s s_s
run' (OffS s r) (S_Off2 s_r) = O_Off2 $ run' r s_r
run' (OffS s r) (S_Off1 s_s) = O_Off1 $ run' s s_s
run' (Rec r) (S_Rec s_r) = O_Rec $ run' r s_r
run' (Weaken r) (S_Weaken s_r) = O_Weaken $ run' r s_r
run' (Var r) (S_Var s_r) = O_Var $ run' r s_r
run' (Ret a) S_Eps = O_Eps a
run' (Lift _) _ = error "Cannot run' O_Lift operations. Use runM' instead or remove all lifts"


-- | `run` cannot deal with lifted computations. This makes it limited to session typed programs without any use of lift.
--
-- This function allows us to evaluate lifted computations, but as a consequence is no longer entirely pure.
runM :: (Monad m, HasConstraint Show s) => STTerm m s ('Cap ctx 'Eps) a -> Stream s -> m (Output s a)
runM st inp = runM' (st I.>>= eps) inp 

-- | Monadic version of `runAll`.
runAllM :: (Monad m, HasConstraint Show s) => STTerm m s ('Cap ctx 'Eps) a -> Stream s -> m [a]
runAllM st stm = fmap evalOutput $ runM st stm

-- | Monad version of `runSingle`
runSingleM :: (Monad m, HasConstraint Show s) => STTerm m s ('Cap ctx 'Eps) a -> Stream s -> m a
runSingleM st stm = fmap (head . evalOutput) $ runM st stm

runM' :: (HasConstraint Show s, Monad m) => STTerm m s r a -> Stream s -> m (Output s a)
runM' (Send a r) (S_Send s_r) = fmap (O_Send a) $ runM' r s_r
runM' (Recv c) (S_Recv a s_r) = fmap (O_Recv a) $ runM' (c a) s_r
runM' (Sel1 s) (S_Sel1 s_s) = fmap O_Sel1 $ runM' s s_s
runM' (Sel2 r) (S_Sel2 s_r) = fmap O_Sel2 $ runM' r s_r
runM' (OffZ s) (S_OffZ s_s) = fmap O_OffZ $ runM' s s_s
runM' (OffS s r) (S_OffS s_s s_r) = pure O_OffS <*> (runM' s s_s) <*> (runM' r s_r)
runM' (OffZ s) (S_Off1 s_s) = fmap O_Off1 $ runM' s s_s
runM' (OffS s r) (S_Off2 s_r) = fmap O_Off2 $ runM' r s_r
runM' (OffS s r) (S_Off1 s_s) = fmap O_Off1 $ runM' s s_s
runM' (Rec r) (S_Rec s_r) = fmap O_Rec $ runM' r s_r
runM' (Weaken r) (S_Weaken s_r) = fmap O_Weaken $ runM' r s_r
runM' (Var r) (S_Var s_r) = fmap O_Var $ runM' r s_r
runM' (Ret a) S_Eps = return $ O_Eps a
runM' (Lift m) stm = m >>= \st -> fmap O_Lift $ runM' st stm   


-- | We use the `Stream` data type to supply input for the receives
-- in a session typed programs.
--
-- We annotate a `Stream` with a capability for the following three reasons:
--
--    1. Each `recv` may return a value of a different type.
--
--    2. Given reason 1 and that we can have branching, we must also be able to branch in the stream.
--
--    3. We can now write a function that recursively generates input for a recursive program
--
--
-- Similar to `STTerm`, `Stream` has a constructor for each session type.
-- Each constructor takes an argument that is another `Stream` type, except
-- for `S_Recv` that takes an additional argument that will be used as input, and
-- `S_Eps` that denotes the end of the stream.
--
--
-- At first it might be confusing which constructors and in what order these constructors
-- should be placed to form a `Stream` that can be used as input for some `STTerm`.
--
-- This is actually not that difficult at all. A `Stream` is session typed and that
-- session type must be equal to the session type of the `STTerm`. As such one merely needs to
-- create a `Stream` that has the same session type and if you don't the type checker will tell you
-- what it incorrect.
--
-- There are two things that you need to be aware of when constructor a `Stream`.
--
--    * The `Stream` constructors for offering (S_OffZ and S_OffS) require that you define input for all branches
--      of the offering. This can be quite cumbersome, so we include a `S_Off1` and `S_Off2` constructor that behave
--      similarly to `S_Sel1` and `S_Sel2`. 
--
--    * You are not guaranteed that a `Stream` can be used for all session typed programs that have the same session type.
--      Specifically when it comes to selection can we not guarantee this. The session type for selection only tells us
--      about which branches could be selected. It does not tell us which branch was selected as this is runtime dependent.
--      
data Stream :: Cap Type -> Type where
  S_Send ::      Stream ('Cap ctx s) ->               Stream ('Cap ctx (a :!> s))
  S_Recv :: a -> Stream ('Cap ctx s) ->               Stream ('Cap ctx (a :?> s))
  S_Sel1 ::      Stream ('Cap ctx s) ->               Stream ('Cap ctx (Sel (s ': xs)))
  S_Sel2 ::      Stream ('Cap ctx (Sel (t ': xs))) -> Stream ('Cap ctx (Sel (s ': t ': xs)))
  S_OffZ ::      Stream ('Cap ctx s) ->               Stream ('Cap ctx (Off '[s]))
  S_OffS ::      Stream ('Cap ctx s) ->               Stream ('Cap ctx (Off (t ': xs))) -> Stream ('Cap ctx (Off (s ': t ': xs)))
  S_Off1 ::      Stream ('Cap ctx s) ->               Stream ('Cap ctx (Off (s ': xs)))
  S_Off2 ::      Stream ('Cap ctx (Off (t ': xs))) -> Stream ('Cap ctx (Off (s ': t ': xs)))
  S_Rec ::       Stream ('Cap (s ': ctx) s) ->        Stream ('Cap ctx (R s))
  S_Weaken ::    Stream ('Cap ctx s) ->               Stream ('Cap (t ': ctx) (Wk s))
  S_Var ::       Stream ('Cap (s ': ctx) s) ->        Stream ('Cap (s ': ctx) V)
  S_Eps ::       Stream ('Cap '[] Eps)

-- | The `Output` data type describes the session type actions that were done
data Output :: Cap Type -> Type -> Type where
  O_Send :: a -> Output ('Cap ctx r) b ->               Output ('Cap ctx (a :!> r)) b
  O_Recv :: a -> Output ('Cap ctx r) b ->               Output ('Cap ctx (a :?> r)) b
  O_Sel1 ::      Output ('Cap ctx s) b ->               Output ('Cap ctx (Sel (s ': xs))) b
  O_Sel2 ::      Output ('Cap ctx (Sel xs)) b ->        Output ('Cap ctx (Sel (s ': xs))) b
  O_OffZ ::      Output ('Cap ctx s) a ->               Output ('Cap ctx (Off '[s])) a
  O_OffS ::      Output ('Cap ctx s) b ->               Output ('Cap ctx (Off (t ': xs))) b -> Output ('Cap ctx (Off (s ': t ': xs))) b
  O_Off1 ::      Output ('Cap ctx s) a ->               Output ('Cap ctx (Off (s ': xs))) a
  O_Off2 ::      Output ('Cap ctx (Off (t ': xs))) a -> Output ('Cap ctx (Off (s ': t ': xs))) a
  O_Rec ::       Output ('Cap (s ': ctx) s) b ->        Output ('Cap ctx (R s)) b
  O_Var ::       Output ('Cap (s ': ctx) s) b ->        Output ('Cap (s ': ctx) V) b
  O_Weaken ::    Output ('Cap ctx s) b ->               Output ('Cap (t ': ctx) (Wk s)) b
  O_Eps :: b ->  Output ('Cap ctx Eps) b
  O_Lift ::      Output s b -> Output s b

-- | Extracts all result values from a given `Output`
evalOutput :: Output s a -> [a]
evalOutput (O_Send _ r) = evalOutput r
evalOutput (O_Recv _ r) = evalOutput r
evalOutput (O_Sel1 s) = evalOutput s
evalOutput (O_Sel2 r) = evalOutput r
evalOutput (O_OffZ s) = evalOutput s
evalOutput (O_OffS s r) = evalOutput s ++ evalOutput r
evalOutput (O_Off1 s) = evalOutput s
evalOutput (O_Off2 r) = evalOutput r
evalOutput (O_Rec s) = evalOutput s
evalOutput (O_Var r) = evalOutput r
evalOutput (O_Weaken r) = evalOutput r
evalOutput (O_Eps a) = [a]
evalOutput (O_Lift s) = evalOutput s


deriving instance (HasConstraint Show s, Show a) => Show (Output s a)
deriving instance (HasConstraint Eq s, Eq a) => Eq (Output s a)
deriving instance (HasConstraint Show s) => Show (Stream s)
deriving instance (HasConstraint Eq s) => Eq (Stream s)
--deriving instance (HasConstraint Ord s, Ord a) => Ord (Output s a)


instance (HasConstraint NFData s, NFData a) => NFData (Output s a) where
  rnf (O_Send a b) = (rnf a) `seq` (rnf b)
  rnf (O_Recv a r) = rnf a `seq` rnf r
  rnf (O_Sel1 s) = rnf s
  rnf (O_Sel2 r) = rnf r
  rnf (O_OffZ s) = rnf s
  rnf (O_OffS s r) = rnf s `seq` rnf r
  rnf (O_Off1 s) = rnf s
  rnf (O_Off2 r) = rnf r
  rnf (O_Rec s) = rnf s
  rnf (O_Var s) = rnf s
  rnf (O_Weaken s) = rnf s
  rnf (O_Eps a) = rnf a 
  rnf (O_Lift s) = rnf s

instance (HasConstraint NFData s) => NFData (Stream s) where
  rnf (S_Send r) = rnf r
  rnf (S_Recv a r) = rnf a `seq` rnf r
  rnf (S_Sel1 s) = rnf s
  rnf (S_Sel2 r) = rnf r
  rnf (S_OffZ s) = rnf s
  rnf (S_OffS s r) = rnf s `seq` rnf r
  rnf (S_Off1 s) = rnf s
  rnf (S_Off2 r) = rnf r
  rnf (S_Rec s) = rnf s
  rnf (S_Var s) = rnf s
  rnf (S_Weaken s) = rnf s
  rnf (S_Eps) = ()


rec2 = S_Rec . S_Rec
rec4 = rec2 . rec2
rec8 = rec4 . rec4
rec16 = rec8 . rec8
rec32 = rec16 . rec16
rec64 = rec32 . rec32
rec128 = rec64 . rec64
rec100 = rec64 . rec32 . rec4

wk2 = S_Weaken . S_Weaken
wk4 = wk2 . wk2
wk8 = wk4 . wk4
wk16 = wk8 . wk8
wk32 = wk16 . wk16
wk64 = wk32 . wk32
wk128 = wk64 . wk64
wk100 = wk64 . wk32 . wk4