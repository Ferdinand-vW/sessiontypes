import SessionTypes
import SessionTypes.Debug

import Test.Program.Simple
import Test.Program.FileServer
import Test.Hspec

main :: IO ()
main = hspec $ do
  describe "runSingle" $ do
    it "returns True" $
      runSingle (inferIdentity prog_sendRecv) (S_Send $ S_Recv True S_Eps) `shouldBe` True

    it "returns the value of the first returned value in a program; '()'" $
      runSingle (inferIdentity prog_branching) (S_Off1 $ S_Send S_Eps) `shouldBe` ()

    it "selects a branch and returns 'c'" $
      runSingle (inferIdentity prog_branching_dual) (S_Sel1 $ S_Recv "c" S_Eps) `shouldBe` "c"

    it "Recurses until a 10 is given" $
      runSingle (inferIdentity prog_recursion) (S_Rec $ S_Recv 7 $ S_Sel2 $ S_Sel1 $ S_Var $ S_Recv 10 $ S_Sel1 $ S_Weaken $ S_Eps) `shouldBe` 10

  describe "runAll" $ do
    it "returns [True]" $
      runAll (inferIdentity prog_sendRecv) (S_Send $ S_Recv True S_Eps) `shouldBe` [True]
    
    it "returns the values returned in all branches; [(),(),()]" $
      runAll (inferIdentity prog_branching) (S_OffS (S_Send S_Eps) $ S_OffS (S_Send S_Eps) $ S_OffZ (S_Send S_Eps)) `shouldBe` [(),(),()]

    it "returns only the final result in a list; [10]" $
      runAll (inferIdentity prog_recursion) (S_Rec $ S_Recv 7 $ S_Sel2 $ S_Sel1 $ S_Var $ S_Recv 10 $ S_Sel1 $ S_Weaken $ S_Eps) `shouldBe` [10]

  describe "run" $ do
    it "returns O_Send followed by O_Recv" $ 
      run (inferIdentity prog_sendRecv) (S_Send $ S_Recv True S_Eps) `shouldBe` (O_Send "c" $ O_Recv True $ O_Eps True)

    it "describes the second branch" $
      run (inferIdentity prog_branching) (S_Off2 $ S_Off1 $ S_Send S_Eps) `shouldBe` (O_Off2 $ O_Off1 $ O_Send True $ O_Eps ())

    it "Recurses until a 10 is given" $
      run (inferIdentity prog_recursion) (S_Rec $ S_Recv 7 $ S_Sel2 $ S_Sel1 $ S_Var $ S_Recv 10 $ S_Sel1 $ S_Weaken $ S_Eps) `shouldBe`
        (O_Rec $ O_Recv 7 $ O_Sel2 $ O_Sel1 $ O_Var $ O_Recv 10 $ O_Sel1 $ O_Weaken $ O_Eps 10)

  describe "runSingleM" $ do
    it "can be used to print something to console" $ do
      s <- runSingleM (client ["test.txt", "doesnotexist.txt"])
        (S_Rec $ S_Sel1 $ S_Send $ S_Recv (Right "hello") $ S_Var $ 
                 S_Sel1 $ S_Send $ S_Recv (Left "File does not exist") $ S_Var $ 
                 S_Sel2 $ S_Sel1 $ S_Weaken $ S_Eps)
      s `shouldBe` ["hello"]

    it "can do any IO action (like readFile)" $ do
      let io = runSingleM server
                (S_Rec $ S_Off1 $ S_Recv "hello.txt" $ S_Send $ S_Var $
                        S_Off1 $ S_Recv "doesnotexist.txt" $ S_Send $ S_Var $
                        S_Off2 $ S_Off1 $ S_Weaken $ S_Eps)
      io `shouldThrow` anyException

  describe "runAllM" $ do
    it "returns more than one result" $ do
      s <- runAllM (client ["text.txt", "doesnotexist.txt"])
        (S_Rec $ S_Sel1 $ S_Send $ S_Recv (Right "hello") $ S_Var $ 
                 S_Sel1 $ S_Send $ S_Recv (Right "text") $ S_Var $ 
                 S_Sel2 $ S_Sel1 $ S_Weaken $ S_Eps)
      s `shouldBe` [["text", "hello"]]

  describe "runM" $ do
    it "Also describes Lifts" $ do
      s <- runM (client ["text.txt", "doesnotexist.txt"])
        (S_Rec $ S_Sel1 $ S_Send $ S_Recv (Right "hello") $ S_Var $ 
                 S_Sel1 $ S_Send $ S_Recv (Left "File does not exist") $ S_Var $ 
                 S_Sel2 $ S_Sel1 $ S_Weaken $ S_Eps)
      s `shouldBe` (O_Rec $ O_Sel1 $ O_Send "text.txt" $ O_Recv (Right "hello") $ O_Var $
                            O_Sel1 $ O_Send "doesnotexist.txt" $ O_Recv (Left "File does not exist") $ O_Lift $ O_Var $
                            O_Sel2 $ O_Sel1 $ O_Weaken $ O_Eps ["hello"])
  
  

    
