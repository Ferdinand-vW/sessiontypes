{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
module Test.Program.FileServer where

import SessionTypes
import SessionTypes.Indexed
import SessionTypes.Debug

import System.Directory

client :: (IxMonadIO m, MonadSession m) => [String] -> m ('Cap ctx (R (Sel '[String :!> Either String String :?> V, Wk Eps]))) ('Cap ctx Eps) [String]
client fnames = recurse $ client' fnames []
  where
    client' [] contents = selN2 >> weaken0 >> eps contents
    client' (fname:fnames) contents = do 
      sel1
      send fname
      eth <- recv

      case eth of
        Left s -> liftIO (putStrLn s) >> var (client' fnames contents) 
        Right s -> var $ client' fnames (s : contents)

server :: (IxMonadIO m, MonadSession m) => m ('Cap ctx (R (Off '[String :?> Either String String :!> V, Wk Eps]))) ('Cap ctx Eps) ()
server = recurseFix $ \f -> do
  offer (do
    fname <- recv

    b <- liftIO $ doesPathExist fname
    if b
      then send (Left "File does not exist") >> f
      else liftIO (readFile fname) >>= \s -> send (Right s) >> f) $
    weaken0 >> eps0

prog :: MonadSession m => m ('Cap ctx (Int :!> Sel '[Eps, Int :!> Eps])) r ()
prog = undefined

prog2 :: MonadSession m => m ('Cap ctx (Sel '[Eps, String :!> Eps, Int :!> Eps])) ('Cap ctx Eps) ()
prog2 = sel >> send "c" >>= eps