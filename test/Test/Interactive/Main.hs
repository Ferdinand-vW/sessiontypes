{-# LANGUAGE ScopedTypeVariables #-}
import Control.SessionTypes.Interactive
import qualified Control.SessionTypes.Indexed as I
import Control.SessionTypes
import Test.Program.FileServer
import Control.Monad.Catch

main = putStrLn "Interactive requires manual testing."

test = do
  -- If entered Right x then result should be
  -- > [x]
  -- If entered Left x then result should be
  -- > x
  -- > []
  res1 <- interactive (empty0 I.>> client ["test.txt"])
  putStrLn $ show res1

  -- There are two possible execution paths to take (disregarding aborting):
  -- > Recurse
  -- ?> Press n to continue or q to quit
  -- n
  -- ?> (L)eft or (R)ight: L
  -- ?> Press n to continue or q to quit
  -- n
  -- ?> Enter value of type [Char]: "hello"
  -- ?> Press n to continue or q to quit.
  -- n
  -- > Lifted
  -- ?> Press n to continue or q to quit
  -- n
  -- > Lifted
  -- ?> Press n to continue or q to quit
  -- n
  -- *** Exception: hello: openFile: does not exist (No such file or directory)
  catch (interactiveStep (empty0 I.>> server) >>= putStrLn . show) $ \(e :: SomeException) -> do
    putStrLn $ show e
    -- > Recurse
    -- ?> Press n to continue or q to quit
    -- n
    -- ?> (L)eft or (R)right: Right
    -- ?> Press n to continue or q to quit
    -- n
    -- > Weaken
    -- ?> Press n to continue or q to quit
    -- n
    -- > Returned: ()
    -- Just ()
    res2 <- interactiveStep (empty0 I.>> server)
    putStrLn $ show res2
    -- It is also possible to abort, in which case we expect 'Nothing' to be printed
    -- > Recurse
    -- ?> Press n to continue or q to quit
    -- q
    -- Nothing
    res3 <- interactiveStep (empty0 I.>> server)
    putStrLn $ show res3