{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
module Test.Program.Normalizable where

import SessionTypes
import SessionTypes.Indexed

left_nested_offer :: MonadSession m => m ('Cap ctx (Off '[Off '[Off '[Eps], Eps], Eps])) ('Cap ctx Eps) ()
left_nested_offer =
  offer (
    offer (
      offZ eps0
    ) eps0
  ) eps0

right_nested_offer :: MonadSession m => m ('Cap ctx (Off '[Eps, Eps, Eps])) ('Cap ctx Eps) ()
right_nested_offer = eps0 <& eps0 <&> eps0

center_nested_offer :: MonadSession m => m ('Cap ctx (Off '[Eps, Off '[Eps], Eps])) ('Cap ctx Eps) ()
center_nested_offer =
  eps0
  <& offZ eps0
  <&> eps0
  

left_nested_select :: MonadSession m => m ('Cap ctx (Sel '[Sel '[Sel '[Eps], Eps], Eps])) ('Cap ctx Eps) ()
left_nested_select = sel2 >> sel1 >> eps0

right_nested_select :: MonadSession m => m ('Cap ctx (Sel '[Eps, Eps, Eps])) ('Cap ctx Eps) ()
right_nested_select = selN3 >> eps0

center_nested_select :: MonadSession m => m ('Cap ctx (Sel '[Eps, Sel '[Eps], Eps])) ('Cap ctx Eps) ()
center_nested_select = selN3 >> eps0

extra_r_and_wk_after :: MonadSession m => m ('Cap ctx (R (R (Sel '[Wk V, Wk (Wk Eps)])))) ('Cap ctx Eps) ()
extra_r_and_wk_after = recurse $ go 1
  where
    go 0 = recurseFix $ \_ -> sel2 >> sel1 >> weaken0 >> weaken0 >> eps0
    go n = recurseFix $ \_ -> do
      sel1
      weaken0
      var (go $ n - 1)

extra_r_and_wk_before :: MonadSession m => m ('Cap ctx (R (R (Sel '[V, Wk (Wk Eps)])))) ('Cap ctx Eps) ()
extra_r_and_wk_before = recurseFix $ \_ -> recurse $ go 1
  where
    go 0 = sel2 >> sel1 >> weaken0 >> weaken0 >> eps0
    go n = do
      sel1
      var (go $ n - 1)

simple_recursion :: MonadSession m => m ('Cap ctx (R (Sel '[V, Wk Eps]))) ('Cap ctx Eps) ()
simple_recursion = recurse $ go 1
      where
        go 0 = selN2 >> weaken0 >> eps0
        go n = sel1 >> var (go $ n - 1)