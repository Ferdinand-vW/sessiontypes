{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
module Test.Program.Simple where

import Control.SessionTypes
import Control.SessionTypes.Indexed

prog_sendRecv :: MonadSession m => m ('Cap ctx (String :!> Bool :?> Eps)) ('Cap ctx Eps) Bool
prog_sendRecv = do
  send "c"
  x <- recv
  eps x

prog_sendRecv_dual :: MonadSession m => m ('Cap ctx (String :?> Bool :!> Eps)) ('Cap ctx Eps) String
prog_sendRecv_dual = do
  x <- recv
  send True
  eps x

prog_branching :: MonadSession m => m ('Cap ctx (Off '[String :!> Eps, Bool :!> Eps, Int :!> Eps])) ('Cap ctx Eps) ()
prog_branching = do
  send "c" <& send True <&> send 1
  eps ()


prog_branching_dual :: MonadSession m => m ('Cap ctx (Sel '[String :?> Eps, Bool :?> Eps, Int :?> Eps])) ('Cap ctx Eps) String
prog_branching_dual = do
  sel1
  x <- recv
  eps x

prog_recursion :: MonadSession m => m ('Cap ctx (R (Int :?> Sel '[Wk Eps, V]))) ('Cap ctx Eps) Int
prog_recursion = recurseFix $ \f -> do
  x <- recv

  if x < 10
    then selN2 >> f
    else sel1 >> weaken0 >> eps x

prog_recursion_dual :: MonadSession m => m ('Cap ctx (R (Int :!> Off '[Wk Eps, V]))) ('Cap ctx Eps) Int
prog_recursion_dual = recurse $ go 0
    where 
      go n = do
        send n
        (weaken0 >> eps n) <&> (var $ go (n + 1))
