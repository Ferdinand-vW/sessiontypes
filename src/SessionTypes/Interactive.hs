{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
-- | This module exposes two functions for interactively evaluation a session typed program
--
-- To run a session you must have two participating actors. In our context, the actors are session typed programs.
-- 
-- Using this module the user will act as one of the actors in the session by suppling values to a receive
--
-- and selecting a branch for offerings.
module SessionTypes.Interactive (
  interactive,
  interactiveStep
) where

import SessionTypes.STTerm
import SessionTypes.Types
import qualified SessionTypes.Indexed as I
import SessionTypes.MonadSession

import Control.Monad.Trans.Maybe (MaybeT(..), runMaybeT)
import Control.Monad.IO.Class    (MonadIO, liftIO)
import Data.Proxy                (Proxy (..))
import Data.Typeable             (Typeable, typeRep)
import Text.Read                 (readMaybe)

-- | For this function tThe user will act as the dual to the given `STTerm`. User interaction is only required
-- when the given program does a receive or an offer.
--
-- A possible interaction goes as follows:
--
-- @
-- prog = do
--  send 5
--  x <- recv
--  offer (eps x) (eps "")
--
-- main = interactive prog
-- @
-- 
-- >> Enter value of type String: "test"
-- >> (L)eft or (R)ight: L
-- > "test"
interactive :: (MonadIO m, HasConstraints '[Read, Show, Typeable] s, Show a) => STTerm m s r a -> m a
interactive (Send _ r) = interactive r
interactive r@(Recv c) = do
    liftIO $ putStr $ "Enter value of type " ++ typeShow r ++ ": "
    ma <- liftIO $ fmap readMaybe getLine
    case ma of
      Nothing -> interactive r
      Just a  -> interactive $ c a
  where typeShow :: forall m ctx a r k b. Typeable a => STTerm m ('Cap ctx (a :?> r)) k b -> String
        typeShow _ = show $ typeRep (Proxy :: Proxy a)
interactive (Sel1 s)     = interactive s
interactive (Sel2 r)     = interactive r
interactive (OffZ s)    = interactive s
interactive (OffS s xs) = do
  liftIO $ putStr $ "(L)eft or (R)ight: "
  lr <- liftIO getLine
  case lr of
    "L"     -> interactive s
    "Left"  -> interactive s
    "R"     -> interactive xs
    "Right" -> interactive xs
    _ -> do
      liftIO $ putStrLn "Invalid option"
      interactive (OffS s xs)
interactive (Rec s)  = interactive s
interactive (Weaken s)  = interactive s
interactive (Var s)  = interactive s
interactive (Lift m) = m >>= interactive
interactive (Ret a)  = return a

-- | Different from `interactive` is that this function gives the user the choice to abort the session
-- after each session typed action. 
--
-- Furthermore, it also prints additional output describing which session typed action occurred.
interactiveStep :: (MonadIO m, HasConstraints '[Read, Show, Typeable] s, Show a) => STTerm m s r a -> m (Maybe a)
interactiveStep st = runMaybeT (interactiveStep' st)


-- Implements interactive stepping. Essentially for every constructor we print a message, 
-- and then allow the user to abort or continue.
-- For receiving and branching we also require more input that needs to be given before allowing to abort/continue.
interactiveStep' :: (MonadIO m, HasConstraints '[Read, Show, Typeable] s, Show a) => STTerm m s r a -> MaybeT m a
interactiveStep' s@(Send a r) = do
  printST s
  waitStep
  interactiveStep' r
interactiveStep' s@(Recv r) = do
  printST s
  ma <- liftIO $ fmap readMaybe getLine
  case ma of
    Nothing -> interactiveStep' s
    Just a -> waitStep >> interactiveStep' (r a)
interactiveStep' s@(Sel1 r) = do
  printST s
  waitStep
  interactiveStep' r
interactiveStep' s@(Sel2 r) = do
  printST s
  waitStep
  interactiveStep' r
interactiveStep' (OffZ r) = interactiveStep' r -- If we see a OffZ then we have already chosen a branch
interactiveStep' s@(OffS r xs) = do
  printST s
  lr <- liftIO getLine
  if lr `elem` ["L","Left"]
    then waitStep >> interactiveStep' r
    else if lr `elem` ["R","Right"]
      then waitStep >> interactiveStep' xs
      else do
        liftIO $ putStrLn "Invalid option"
        interactiveStep' (OffS s xs)
interactiveStep' s@(Rec r) = do
  printST s
  waitStep
  interactiveStep' r
interactiveStep' s@(Weaken r) = do
  printST s
  waitStep
  interactiveStep' r
interactiveStep' s@(Var r) = do
  printST s
  waitStep
  interactiveStep' r
interactiveStep' s@(Lift m) = do
  printST s
  waitStep
  MaybeT $ m >>= \st -> runMaybeT $ interactiveStep' st
interactiveStep' s@(Ret a) = do
  printST s
  return a
  
-- Prints a different message for each constructor of `STTerm`
printST :: (MonadIO m, HasConstraints [Typeable, Show] s, Show a) => STTerm m s r a -> MaybeT m ()
printST (Send a _)     = liftIO $ putStrLn $ "> Send value " ++ show a
printST r@(Recv _)     = liftIO $ putStr $ "?> Enter value of type " ++ typeShow r ++ ": "
  where typeShow :: forall m ctx a r k b. Typeable a => STTerm m ('Cap ctx (a :?> r)) k b -> String
        typeShow _ = show $ typeRep (Proxy :: Proxy a)
printST (Sel1 _)      = liftIO $ putStrLn "> Select1"
printST (Sel2 _)      = liftIO $ putStrLn "> Select2"
printST (OffZ _)     = return ()
printST (OffS _ _) = liftIO $ putStr $ "?> (L)eft or (R)ight: "
printST (Rec _)        = liftIO $ putStrLn "> Recurse"
printST (Weaken _)        = liftIO $ putStrLn "> Weaken"
printST (Var _)        = liftIO $ putStrLn "> Var"
printST (Lift _)       = liftIO $ putStrLn $ "> Lifted"
printST (Ret a)        = liftIO $ putStrLn $ "> Returned: " ++ show a

-- Gives the user the option to quit early by pressing q
-- or to continue by pressing n.
-- We use the maybe monad to implement aborting early.
waitStep :: MonadIO m => MaybeT m ()
waitStep = do
  liftIO $ putStrLn "?> Press n to continue or q to quit."
  line <- liftIO $ getLine
  case line of
    "n" -> return ()
    "q" -> MaybeT $ return Nothing
    _ -> waitStep