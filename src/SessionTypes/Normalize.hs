{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE RankNTypes #-}
-- | This module provides a type class for normalizing session typed programs.
--
-- With normalizing we mean that we apply rewrites to a session typed program until we can no longer do so
-- and that do not change the semantics of the program.
--
-- The motivation for this module is that for two session typed programs to run a session they must be dual.
-- Sometimes, one of these programs might not have a session type that is dual to the session type of the other program,
--
-- but we can rewrite the program and therefore also the session type such that it is. It is of course important that we do not
-- alter the semantics of the program when rewriting it. For that reason, any rewrite that we may apply must be isomorphic.
--
-- A rewrite is isomorphic if we have two programs \p\ and \p'\, we can do a rewrite from \p\ to \p'\ and from \p'\ to \p\.
--
-- For now two types of rewrites are applied: Elimination of recursive types and flattening of branches.
module SessionTypes.Normalize (
  Normalize(..),
  Flatten(..),
  ElimRec(..),
) where

import SessionTypes.STTerm
import SessionTypes.Types
import Data.Proxy (Proxy (..))

-- | Type class for rewriting an `STTerm` to its normal form
--
-- The type class has a single instance that is constrained with two type classes.
-- One for each type of rewrite.
class Normalize s s'' | s -> s'' where
  normalize :: Monad m => STTerm m s ('Cap '[] Eps) a -> STTerm m s'' ('Cap '[] Eps) a
  
instance (Flatten s s', ElimRec s' s'') => Normalize s s'' where
  normalize = elimRec . flatten


-------------------------------------------
-- Eliminates unused recursion constructors
-------------------------------------------

-- | Type class for eliminating unused recursive types.
--
-- The function `elimRec` traverses a given `STTerm`. While doing so, it will attempt to remove constructors annotated with `R` or `Wk` from the program
-- if in doing so does not change the behavior of the program.
--
-- For example, in the following session type we may remove the inner `R` and the `Wk`. 
--
-- > R (R (Wk V))
--
-- We have that the outer `R` matches the recursion variable because of the use of `Wk`. 
--
-- That means the inner `R` does not match any recursion variable (the `R` is unused) and therefore may it and its corresponding constructor be removed from the `STTerm` program.
--
-- We also remove the `Wk`, because the session type pushed into the context by the inner `R` has also been removed.
-- 
-- The generated session type is
--
-- > R V
class ElimRec s s' | s -> s' where
  elimRec :: Monad m => STTerm m s r a -> STTerm m s' r a

instance (el ~ ElimRecAllPath s, ElimRec' s s' el) => ElimRec s s' where
  elimRec = elimRec' (Proxy :: Proxy el)


-- Type class that does the actual rewriting of the AST
-- It takes an extra type parameter, which tells us when to remove a `R`
-- or a `Wk`. This is computed using the type family `ElimRecAllPath`
class ElimRec' s s' (rml :: Cap Bool) | s rml -> s' where
  elimRec' :: Monad m => Proxy rml -> STTerm m s r a -> STTerm m s' r a


-- The only instances of interest are those of `R` and `Wk`. The other
-- instances only traverse the AST
instance ElimRec' ('Cap ctx r) ('Cap ctx' r') rml => 
         ElimRec' ('Cap ctx (a :!> r)) ('Cap ctx' (a :!> r')) rml where
  elimRec' rml (Send a r) = Send a $ elimRec' rml r

instance ElimRec' ('Cap ctx r) ('Cap ctx' r') rml => 
         ElimRec' ('Cap ctx (a :?> r)) ('Cap ctx' (a :?> r')) rml where
  elimRec' rml (Recv r) = Recv $ \a -> elimRec' rml (r a)

-- We need two instances for each branching session type
-- One handling the singleton case and another for having at least
-- two branches. 
instance ElimRec' ('Cap ctx s) 
                  ('Cap ctx' s') 
                  ('Cap rmctx rm) => 
         ElimRec' ('Cap ctx (Sel '[s])) 
                  ('Cap ctx' (Sel '[s'])) 
                  ('Cap rmctx (Sel '[rm])) where
  elimRec' _ (Sel1 s) = Sel1 $ elimRec' (Proxy :: Proxy ('Cap rmctx rm)) s

instance (ElimRec' ('Cap ctx s) 
                   ('Cap ctx' s') 
                   ('Cap rmctx rm), 
          ElimRec' ('Cap ctx (Sel (t ': xs))) 
                   ('Cap ctx' (Sel (t' ': xs'))) 
                   ('Cap rmctx (Sel rmxs))) => 
          ElimRec' ('Cap ctx (Sel (s ': t ': xs))) 
                   ('Cap ctx' (Sel (s' ': t' ': xs'))) 
                   ('Cap rmctx (Sel (rm ': rmxs))) where
  elimRec' _ (Sel1 s) = Sel1 $ elimRec' (Proxy :: Proxy ('Cap rmctx rm)) s
  elimRec' _ (Sel2 xs) = Sel2 $ elimRec' (Proxy :: Proxy ('Cap rmctx (Sel rmxs))) xs

instance ElimRec' ('Cap ctx s) 
                  ('Cap ctx' s') 
                  ('Cap rmctx rm) => 
         ElimRec' ('Cap ctx (Off '[s])) 
                  ('Cap ctx' (Off '[s'])) 
                  ('Cap rmctx (Off '[rm])) where
  elimRec' _ (OffZ s) = OffZ $ elimRec' (Proxy :: Proxy ('Cap rmctx rm)) s

instance (ElimRec' ('Cap ctx s) ('Cap ctx' s') ('Cap rmctx rm), 
          ElimRec' ('Cap ctx (Off (t ': xs))) 
                   ('Cap ctx' (Off (t' ': xs'))) 
                   ('Cap rmctx (Off rmxs))) => 
         ElimRec' ('Cap ctx (Off (s ': t ': xs))) 
                  ('Cap ctx' (Off (s' ': t' ': xs'))) 
                  ('Cap rmctx (Off (rm ': rmxs))) where
  elimRec' _ (OffS s xs) = 
    OffS (elimRec' (Proxy :: Proxy ('Cap rmctx rm)) s)
           (elimRec' (Proxy :: Proxy ('Cap rmctx (Off rmxs))) xs)

-- For this instance we have computed that we must not remove this `R`
-- So we write a `Rec` and do a recursive call on its argument
instance (ElimRec' ('Cap (s ': ctx) s) 
                   ('Cap (s' ': ctx') s') 
                   ('Cap (rml ': rmctx) rml)) => 
          ElimRec' ('Cap ctx (R s)) 
                   ('Cap ctx' (R s')) 
                   ('Cap rmctx ('True :!> rml))  where
  elimRec' _ (Rec s) = Rec $ elimRec' (Proxy :: Proxy ('Cap (rml ': rmctx) rml)) s

-- In this case we have determined that the `R` must be removed.
-- So all we do is a recursive call on `s`
instance (ElimRec' ('Cap (s ': ctx) s) 
                   ('Cap ctx' s') 
                   ('Cap rmctx rml)) => 
          ElimRec' ('Cap ctx (R s)) 
                   ('Cap ctx' s') 
                   ('Cap rmctx ('False :!> rml)) where
  elimRec' _ (Rec s) = elimRec' (Proxy :: Proxy ('Cap rmctx rml)) s

-- When keeping the `Wk` we must account for the possibility that
-- an other `R` or `Wk` lower in the AST may have been removed. In that case
-- we can't keep `t` on top of the context as it will still contain that `R`
-- and `Wk`. We use `ApplyElimRecPath` to compute which `R` and `Wk` are supposed
-- to be removed from `t`. The result is then placed on top of the context.
instance (ApplyElimRecPath t rm' ~ t', 
          ElimRec' ('Cap ctx s) 
                   ('Cap ctx' s') 
                   ('Cap rmctx rml)) => 
          ElimRec' ('Cap (t ': ctx) (Wk s)) 
                   ('Cap (t' ': ctx') (Wk s')) 
                   ('Cap (rm' ': rmctx) ('True :!> rml)) where
  elimRec' _ (Weaken s) = Weaken $ elimRec' (Proxy :: Proxy ('Cap rmctx rml)) s

instance (ElimRec' ('Cap ctx s) 
                   ('Cap ctx' s')
                   ('Cap rmctx rml)) => 
          ElimRec' ('Cap (t ': ctx) (Wk s))
                   ('Cap ctx' s')
                   ('Cap rmctx ('False :!> rml)) where
  elimRec' _ (Weaken s) = elimRec' (Proxy :: Proxy ('Cap rmctx rml)) s

instance ElimRec' ('Cap (s ': ctx) s) 
                  ('Cap (s' ': ctx') s') 
                  ('Cap (rm ': rmctx) rm) => 
         ElimRec' ('Cap (s ': ctx) V) 
                  ('Cap (s' ': ctx') V) 
                  ('Cap (rm ': rmctx) V)  where
  elimRec' _ (Var s) = Var $ elimRec' (Proxy :: Proxy ('Cap (rm ': rmctx) rm)) s

instance ElimRec' ('Cap '[] Eps) ('Cap '[] Eps) ('Cap '[] Eps) where
  elimRec' _ (Ret a) = Ret a 
  elimRec' _ (Lift m) = error "was a lift"

---------------------------------------------------------------------
-- Type families used to compute which R's and Wk's should be removed
---------------------------------------------------------------------

-- Type family to be applied to a capability that calculates a session type
-- that tells us if an `R` or a `Wk` should be removed.
type family ElimRecAllPath c where
  ElimRecAllPath ('Cap ctx s) = 'Cap (MapElimRecAllPath ctx Z) (ElimRecAllPathST s Z)


type family ElimRecAllPathST s n where
  ElimRecAllPathST (a :!> r) n = ElimRecAllPathST r n
  ElimRecAllPathST (a :?> r) n = ElimRecAllPathST r n
  ElimRecAllPathST (Sel xs) n = Sel (MapElimRecAllPath xs n)
  ElimRecAllPathST (Off xs) n = Off (MapElimRecAllPath xs n)
-- An `R` may only be removed if it does not correspond to a `V`
  ElimRecAllPathST (R s) n = KeepRPath (R s) (HasPathToV s (S Z)) n
-- An `Wk` may only be removed if an `R` above it was removed
  ElimRecAllPathST (Wk s) (S n) = KeepWkPath (Wk s) (HasPathToV s n) (S n)
  ElimRecAllPathST (Wk s) n = 'False :!> ElimRecAllPathST s n
  ElimRecAllPathST V n = V
  ElimRecAllPathST Eps n = Eps

type family MapElimRecAllPath xs n where
  MapElimRecAllPath '[] n = '[]
  MapElimRecAllPath (s ': xs) n = ElimRecAllPathST s n ': MapElimRecAllPath xs n

-- If we remove a `R` we also have to consider removing any corresponding `Wk`.
-- However, a `Wk` might be incorrectly marked to not be removed since 
-- it could be matched to an outer `R`. We use `DeleteWkPath` to also account for this
type family KeepRPath s b n where
  KeepRPath (R s) 'True n = ('True :!> (ElimRecAllPathST s (S n)))
  KeepRPath (R s) 'False n = ('False :!> ((ElimRecAllPathST s n) `MergePath` (DeleteWkPath s (S Z) n)))

type family KeepWkPath s b n where
  KeepWkPath (Wk s) 'True (S n) = ('True :!> (ElimRecAllPathST s n))
  KeepWkPath (Wk s) 'False n = ('True :!> ElimRecAllPathST s (S n))

-- Type family that can calcuate for an `R` whether there exists a recursion
-- variable that corresponds to that `R`. The type family assumes that it is applied
-- to the body of the `R`.
-- It takes two arguments: a session type and a natural number.
-- The natural number is incremented on seeing a `R`
-- and decremented on seeing a `Wk`. Then if it is (S Z)
-- we know that we have incremented as often as decremented.
-- We therefore also know that the R from where this type family
-- was called reaches a V
type family HasPathToV s n :: Bool where
  HasPathToV (a :!> r) n = HasPathToV r n
  HasPathToV (a :?> r) n = HasPathToV r n
  HasPathToV (Sel '[s]) n = HasPathToV s n
  HasPathToV (Sel (s ': xs)) n = HasPathToV s n `Or` HasPathToV (Sel xs) n
  HasPathToV (Off '[s]) n = HasPathToV s n
  HasPathToV (Off (s ': xs)) n = HasPathToV s n `Or` HasPathToV (Off xs) n
  HasPathToV (R s) n = HasPathToV s (S n)
  HasPathToV (Wk s) (S n) = HasPathToV s n
  HasPathToV (Wk s) n = 'False
  HasPathToV V (S Z) = 'True
  HasPathToV V n = 'False
  HasPathToV Eps n = 'False


  
-- Determines whether a `Wk` should be removed
-- It takes three arguments: a session type and two natural numbers.
-- The first Nat 
type family DeleteWkPath s n k where
  DeleteWkPath (a :!> r) n k = DeleteWkPath r n k
  DeleteWkPath (a :?> r) n k = DeleteWkPath r n k
  DeleteWkPath (Sel xs) n k = Sel (MapDeleteWkPath xs n k)
  DeleteWkPath (Off xs) n k = Off (MapDeleteWkPath xs n k)
  DeleteWkPath (R s) n k = 'True :!> (DeleteWkPath s (S n) (S k))
  DeleteWkPath (Wk Eps) (S Z) (S Z) = 'True :!> Eps
  DeleteWkPath (Wk s) (S Z) k = 'False :!> Eps
  DeleteWkPath (Wk s) (S n) (S k) = 'True :!> (DeleteWkPath s n k)
  DeleteWkPath V n k = V
  DeleteWkPath Eps n k = Eps

type family MapDeleteWkPath xs n k where
  MapDeleteWkPath '[] n k = '[]
  MapDeleteWkPath (s ': xs) n k = DeleteWkPath s n k ': MapDeleteWkPath xs n k

type family MergePath l r where
  MergePath (b1 :!> l) (b2 :!> r) = Not (Not b1 `Or` Not b2) :!> MergePath l r
  MergePath (Sel xs) (Sel ys) = Sel (MapMergePath xs ys)
  MergePath (Off xs) (Off ys) = Off (MapMergePath xs ys)
  MergePath Eps s = s
  MergePath s Eps = s
  MergePath V s = s
  MergePath s V = s

type family MapMergePath l r where
  MapMergePath '[] '[] = '[]
  MapMergePath (s ': xs) (r ': ys) = MergePath s r ': MapMergePath xs ys

-- Given a session type that marks which `R` and `Wk` should be removed
-- we rewrite the session type
type family ApplyElimRecPath s ml where
  ApplyElimRecPath (a :!> r) ml = a :!> ApplyElimRecPath r ml
  ApplyElimRecPath (a :?> r) ml = a :?> ApplyElimRecPath r ml
  ApplyElimRecPath (Sel xs) (Sel ml) = Sel (MapApplyElimRecPath xs ml)
  ApplyElimRecPath (Off xs) (Off ml) = Off (MapApplyElimRecPath xs ml)
  ApplyElimRecPath (R s) ('True :!> ml) = R (ApplyElimRecPath s ml)
  ApplyElimRecPath (R s) ('False :!> ml) = ApplyElimRecPath s ml
  ApplyElimRecPath (Wk s) ('True :!> ml) = Wk (ApplyElimRecPath s ml)
  ApplyElimRecPath (Wk s) ('False :!> ml) = ApplyElimRecPath s ml
  ApplyElimRecPath s ml = s

type family MapApplyElimRecPath xs ml where
  MapApplyElimRecPath '[] '[] = '[]
  MapApplyElimRecPath (s ': xs) (m ': ml) = ApplyElimRecPath s m ': MapApplyElimRecPath xs ml


-- | Type class for flattening branches
--
-- The function `flatten` takes and traverses a `STTerm`. 
-- If it finds a branching session type that has a branch
-- starting with another branching of the same type, then it will extract the branches of the inner branching
-- and inserts these into the outer branching. This is similar to flattening a list of lists to a larger list.
--
-- For example:
--
-- > Sel '[a,b, Sel '[c,d], e]
--
-- becomes
--
-- > Sel '[a,b,c,d,e]
--
-- This only works if the inner branching has the same type as the outer branch (Sel in Sel or Off in Off).
--
-- Also, for now this rewrite only works if one of the branching of the outer branch starts with a new branching.
--
-- For example:
--
-- > Sel '[a,b, Int :!> Sel '[c,d],e]
--
-- does not become
--
-- > Sel '[a,b,Int :!> c, Int :!> d, e]
--
-- This is something that will be added in the future.
class Flatten s s' | s -> s' where
  flatten :: Monad m => STTerm m s r a -> STTerm m s' r a

instance (rwl ~ ListRewrites s, Flatten' s s' rwl) => Flatten s s' where
  flatten = flatten' (Proxy :: Proxy rwl)

class Flatten' s s' rwl | s rwl -> s' where
  flatten' :: Monad m => Proxy rwl -> STTerm m s r a -> STTerm m s' r a


instance Flatten' ('Cap ctx (Sel ys)) 
                ('Cap ctx' (Sel ys')) 
                ('Cap nctx rwl) => 
         Flatten' ('Cap ctx (Sel '[Sel ys])) 
                ('Cap ctx' (Sel ys')) 
                ('Cap nctx ((Sel '[ 'True :!> rwl]))) where
  flatten' _ (Sel1 s) = flatten' (Proxy :: Proxy ('Cap nctx rwl)) s

instance (Flatten' ('Cap ctx (Sel '[y])) 
                 ('Cap ctx' (Sel '[y']))
                 ('Cap nctx rw_y), 
          Flatten' ('Cap ctx (Sel (x ': xs))) 
                 ('Cap ctx' (Sel (x' ': xs'))) 
                 ('Cap nctx (Sel rw_xs))) => 
          Flatten' ('Cap ctx (Sel (Sel '[y] ': x ': xs))) 
                 ('Cap ctx' (Sel (y' ': x' ': xs'))) 
                 ('Cap nctx (Sel ('True :!> rw_y ': rw_xs))) where
  flatten' _ (Sel1 s) =
    case flatten' (Proxy :: Proxy ('Cap nctx rw_y)) s of
      Sel1 s' -> Sel1 s'
  flatten' _ (Sel2 s) = Sel2 $ flatten' (Proxy :: Proxy ('Cap nctx (Sel rw_xs))) s

instance (Flatten' ('Cap ctx (Sel '[s])) 
                 ('Cap ctx' (Sel '[s'])) 
                 ('Cap nctx (Sel '[rw_s])), 
          Flatten' ('Cap ctx (Sel (Sel (z ': ys) ': x ': xs))) 
                 ('Cap ctx' (Sel (z' ': xss))) 
                 ('Cap nctx (Sel (True :!> (Sel rw_ys) ': rw_xss)))) => 
          Flatten' ('Cap ctx (Sel (Sel (s ': z ': ys) ': x ': xs))) 
                 ('Cap ctx' (Sel (s' ': z' ': xss))) 
                 ('Cap nctx (Sel ('True :!> Sel (rw_s ': rw_ys) ': rw_xss))) where
                            -- Using singleSel we enforce the branching denoted by `Sel1 s` to describe
                            -- only a single branch. Otherwise, there would be an ambigeous type variable representing
                            -- the 'other branches', which do not exist. This would prevent us from using flatten on (Sel1 s),
                            -- since we would not be able to describe a constraint matching this application. 
  flatten' _ (Sel1 (Sel1 s)) = Sel1 $ singleSel (Sel1 s) (Proxy :: Proxy ('Cap nctx (Sel '[rw_s])))
  flatten' _ (Sel1 (Sel2 s)) = Sel2 $ flatten' (Proxy :: Proxy ('Cap nctx (Sel (True :!> Sel rw_ys ': rw_xss)))) 
                                        (instSelApp (Sel1 s) (Proxy :: Proxy (x ': xs)))
  flatten' _ (Sel2 s) = Sel2 $ flatten' (Proxy :: Proxy ('Cap nctx (Sel (True :!> Sel rw_ys ': rw_xss)))) 
                                (instSelPrep (Proxy :: Proxy (Sel (z ': ys))) s)

singleSel :: Monad m => Flatten' ('Cap ctx (Sel '[s])) ('Cap ctx' (Sel '[s'])) ('Cap nctx (Sel '[rw_s])) =>
             STTerm m ('Cap ctx (Sel '[s])) r a -> Proxy ('Cap nctx (Sel '[rw_s])) -> STTerm m ('Cap ctx' s') r a
singleSel st p = case flatten' p st of
  (Sel1 s') -> s'

-- Helper functions for append and prepending to a select when this can not only be done using
-- the constructors of STTerm
instSelApp :: STTerm m ('Cap ctx (Sel '[x])) r a -> Proxy ys -> STTerm m ('Cap ctx (Sel (x ': ys))) r a
instSelApp (Sel1 s) _ = Sel1 s

instSelPrep :: Proxy y -> STTerm m ('Cap ctx (Sel (x ': xs))) r a -> STTerm m ('Cap ctx (Sel (y ': x ': xs))) r a
instSelPrep _ s = Sel2 s

instance Flatten' ('Cap ctx (Off ys)) 
                ('Cap ctx' (Off ys')) 
                ('Cap nctx rwl) => 
         Flatten' ('Cap ctx (Off '[Off ys])) 
                ('Cap ctx' (Off ys')) 
                ('Cap nctx (Off '[ 'True :!> rwl])) where
  flatten' _ (OffZ s) = flatten' (Proxy :: Proxy ('Cap nctx rwl)) s

instance (Flatten' ('Cap ctx (Off '[s])) 
                 ('Cap ctx' (Off '[s'])) 
                 ('Cap nctx rwl_s), 
          Flatten' ('Cap ctx (Off (x ': xs))) 
                 ('Cap ctx' (Off (x' ': xs'))) 
                 ('Cap nctx (Off rwl_xs))) => 
          Flatten' ('Cap ctx (Off (Off '[s] ': x ': xs))) 
                 ('Cap ctx' (Off (s' ': x' ': xs'))) 
                 ('Cap nctx (Off ('True :!> rwl_s ': rwl_xs))) where
  flatten' _ (OffS (OffZ s) xs) = 
    case flatten' (Proxy :: Proxy ('Cap nctx rwl_s)) (OffZ s) of
      (OffZ s') -> OffS s' (flatten' (Proxy :: Proxy ('Cap nctx (Off rwl_xs))) xs)

instance (Flatten' ('Cap ctx (Off '[s]))
                 ('Cap ctx' (Off '[s'])) 
                 ('Cap nctx (Off '[rwl_s])), 
          Flatten' ('Cap ctx (Off (Off (z ': ys) ': x ': xs))) 
                 ('Cap ctx' (Off (z' ': xss))) 
                 ('Cap nctx (Off ('True :!> (Off rwl_ys) ': rw_xs)))) => 
          Flatten' ('Cap ctx (Off (Off (s ': z ': ys) ': x ': xs))) 
                 ('Cap ctx' (Off (s' ': z' ': xss))) 
                 ('Cap nctx (Off ('True :!> (Off (rwl_s ': rwl_ys)) ': rw_xs))) where
  flatten' _ (OffS (OffS s ys) xs) = 
    case flatten' (Proxy :: Proxy ('Cap nctx (Off '[rwl_s]))) (OffZ s) of
      OffZ s' -> OffS s' $ flatten' (Proxy :: Proxy ('Cap nctx (Off ('True :!> (Off rwl_ys) ': rw_xs)))) (OffS ys xs)

------------------------------------------------------------
-- Traverse AST and apply flatten'
------------------------------------------------------------

instance Flatten' ('Cap ctx s) 
                ('Cap ctx' s') 
                ('Cap nctx rwl) => 
         Flatten' ('Cap ctx (Sel '[s])) 
                ('Cap ctx' (Sel '[s'])) 
                ('Cap nctx (Sel '[ 'False :!> rwl])) where
  flatten' _ (Sel1 s) = Sel1 $ flatten' (Proxy :: Proxy ('Cap nctx rwl)) s

instance (Flatten' ('Cap ctx s) 
                 ('Cap ctx' s') 
                 ('Cap nctx rw_s), 
          Flatten' ('Cap ctx (Sel (r ': xs))) 
                 ('Cap ctx' (Sel (r' ': xs'))) 
                 ('Cap nctx (Sel rw_xs))) => 
          Flatten' ('Cap ctx (Sel (s ': r ': xs))) 
                 ('Cap ctx' (Sel (s' ': r' ': xs'))) 
                 ('Cap nctx (Sel ('False :!> rw_s ': rw_xs))) where
  flatten' _ (Sel1 s) = Sel1 $ flatten' (Proxy :: Proxy ('Cap nctx rw_s)) s
  flatten' _ (Sel2 s) = Sel2 $ flatten' (Proxy :: Proxy ('Cap nctx (Sel rw_xs))) s

instance Flatten' ('Cap ctx s) 
                ('Cap ctx' s') 
                ('Cap nctx rwl) => 
         Flatten' ('Cap ctx (Off '[s])) 
                ('Cap ctx' (Off '[s'])) 
                ('Cap nctx (Off '[ 'False :!> rwl])) where
  flatten' _ (OffZ s) = OffZ $ flatten' (Proxy :: Proxy ('Cap nctx rwl)) s

instance (Flatten' ('Cap ctx s) 
                 ('Cap ctx' s') 
                 ('Cap nctx rwl_s), 
          Flatten' ('Cap ctx (Off (t ': xs))) 
                 ('Cap ctx' (Off (t' ': xs'))) 
                 ('Cap nctx (Off rwl_r))) => 
          Flatten' ('Cap ctx (Off (s ': t ': xs))) 
                 ('Cap ctx' (Off (s' ': t' ': xs'))) 
                 ('Cap nctx (Off ('False :!> rwl_s ': rwl_r))) where
  flatten' _ (OffS s xs) = 
    OffS (flatten' (Proxy :: Proxy ('Cap nctx rwl_s)) s) 
           (flatten' (Proxy :: Proxy ('Cap nctx (Off rwl_r))) xs)

instance Flatten' ('Cap ctx r) 
                ('Cap ctx' r') 
                rwl => 
         Flatten' ('Cap ctx (a :!> r)) 
                ('Cap ctx' (a :!> r')) 
                rwl where
  flatten' p (Send a (Lift m)) = Send a $ Lift $ do
    st <- m
    return $ flatten' p st
  flatten' p (Send a r) = Send a $ flatten' p r

instance Flatten' ('Cap ctx r) 
                ('Cap ctx' r') 
                rwl => 
         Flatten' ('Cap ctx (a :?> r)) 
                ('Cap ctx' (a :?> r')) 
                rwl where
  flatten' p (Recv r) = Recv $ \x -> 
    case r x of
      (Lift m) -> Lift $ do
        st <- m
        return $ flatten' p st
      _ -> flatten' p $ r x

instance Flatten' ('Cap (s ': ctx) s) 
                ('Cap (s' ': ctx') s') 
                ('Cap (norm ': nctx) norm) => 
         Flatten' ('Cap ctx (R s)) 
                ('Cap ctx' (R s')) 
                ('Cap nctx norm) where
  flatten' _ (Rec s) = Rec $ flatten' (Proxy :: Proxy ('Cap (norm ': nctx) norm)) s

-- Similar to the ElimRec case, 
-- the `t` at the top of the context might be invalidated after 
-- rewriting the argument to `Wk`. Hence, we also have to rewrite
-- `t`.
instance (RewriteTypes t ~ t', 
          Flatten' ('Cap ctx s) 
                 ('Cap ctx' s') 
                 ('Cap nctx norm)) => 
          Flatten' ('Cap (t ': ctx) (Wk s)) 
                 ('Cap (t' ': ctx') (Wk s')) 
                 ('Cap (k ': nctx) norm) where
  flatten' _ (Weaken s) = Weaken $ flatten' (Proxy :: Proxy ('Cap nctx norm)) s

instance Flatten' ('Cap (s ': ctx) s) 
                ('Cap (s' ': ctx') s') 
                ('Cap (norm ': nctx) norm) => 
         Flatten' ('Cap (s ': ctx) V) 
                ('Cap (s' ': ctx') V) 
                ('Cap (norm ': nctx) V) where
  flatten' _ (Var s) = Var $ flatten' (Proxy :: Proxy ('Cap (norm ': nctx) norm)) s

instance Flatten' ('Cap ctx Eps) ('Cap ctx Eps) ('Cap nctx Eps) where
  flatten' _ (Ret a) = Ret a


type family ListRewrites c where
  ListRewrites ('Cap ctx s) = 'Cap (MapListRewritesCtx ctx) (ListRewritesST s)

type family MapListRewritesCtx ctx where
  MapListRewritesCtx '[] = '[]
  MapListRewritesCtx (s ': xs) = ListRewritesST s ': MapListRewritesCtx xs

-- Returns a session type marking where we can do an flatteniative rewrite
type family ListRewritesST s where
  ListRewritesST (Sel xs) = Sel (RewriteFlatten (MapListRewritesCtx xs))
  ListRewritesST (Off xs) = Off (RewriteFlatten (MapListRewritesCtx xs))
  ListRewritesST (a :!> r) = ListRewritesST r
  ListRewritesST (a :?> r) = ListRewritesST r
  ListRewritesST (R s) = ListRewritesST s
  ListRewritesST (Wk s) = ListRewritesST s
  ListRewritesST V = V
  ListRewritesST Eps = Eps

-- Determines whether we can do a flatteniative rewrite
type family RewriteFlatten s where
  RewriteFlatten '[] = '[]
  RewriteFlatten (Sel xs ': ys) = ('True :!> Sel xs) ': RewriteFlatten ys
  RewriteFlatten (Off xs ': ys) = ('True :!> Off xs) ': RewriteFlatten ys
  RewriteFlatten (s ': ys) = ('False :!> s) ': RewriteFlatten ys


-- Does a full flatteniative rewrite
type family RewriteTypes s where
  RewriteTypes (a :!> r) = a :!> RewriteTypes r
  RewriteTypes (a :?> r) = a :?> RewriteTypes r
  RewriteTypes (Sel (Sel xs ': ys)) = RewriteTypes (Sel (xs `Append` ys))
  RewriteTypes (Sel (x ': xs)) = Sel (x ': MapRewriteTypes xs)
  RewriteTypes (Off (Off xs ': ys)) = RewriteTypes (Off (xs `Append` ys))
  RewriteTypes (Off (x ': xs)) = Off (x ': MapRewriteTypes xs)
  RewriteTypes (R s) = R (RewriteTypes s)
  RewriteTypes (Wk s) = Wk (RewriteTypes s)
  RewriteTypes V = V
  RewriteTypes Eps = Eps

type family MapRewriteTypes xs where
  MapRewriteTypes '[] = '[]
  MapRewriteTypes (s ': xs) = RewriteTypes s ': MapRewriteTypes xs