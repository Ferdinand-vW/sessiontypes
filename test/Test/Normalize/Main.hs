{-# LANGUAGE DataKinds #-}
import SessionTypes
import SessionTypes.Debug
import SessionTypes.Normalize

import Test.Program.Normalizable
import Test.Hspec


main = hspec $ do
  describe "Normalize" $ do
    it "rewrites a left nested offering to a right nested offering" $ do
      run (normalize (inferIdentity left_nested_offer)) (S_OffS S_Eps $ S_OffS S_Eps $ S_OffZ S_Eps)
        `shouldBe` run (inferIdentity right_nested_offer) (S_OffS S_Eps $ S_OffS S_Eps $ S_OffZ S_Eps)

    it "rewrites a center nested offering to a right nested offering" $ do
      run (normalize $ inferIdentity center_nested_offer) (S_OffS S_Eps $ S_OffS S_Eps $ S_OffZ S_Eps)
        `shouldBe` run (inferIdentity right_nested_offer) (S_OffS S_Eps $ S_OffS S_Eps $ S_OffZ S_Eps)

    it "rewrites a left nested selection to a right nested selection" $ do
      run (normalize (inferIdentity left_nested_select)) (S_Sel2 $ S_Sel2 $ S_Sel1 S_Eps)
        `shouldBe` run (inferIdentity right_nested_select) (S_Sel2 $ S_Sel2 $ S_Sel1 S_Eps)

    it "rewrites a center nested selection to a right nested selection" $ do
      run (normalize $ inferIdentity center_nested_select) (S_Sel2 $ S_Sel2 $ S_Sel1 S_Eps)
        `shouldBe` run (inferIdentity right_nested_select) (S_Sel2 $ S_Sel2 $ S_Sel1 S_Eps)

    it "eliminates unused R's and Wk's" $ do
      [run (normalize $ inferIdentity extra_r_and_wk_after) (S_Rec $ S_Sel1 $ S_Var $ S_Sel2 $ S_Sel1 $ S_Weaken S_Eps),
       run (normalize $ inferIdentity extra_r_and_wk_before) (S_Rec $ S_Sel1 $ S_Var $ S_Sel2 $ S_Sel1 $ S_Weaken S_Eps)]
        `shouldMatchList` 
        [run (inferIdentity simple_recursion) (S_Rec $ S_Sel1 $ S_Var $ S_Sel2 $ S_Sel1 $ S_Weaken S_Eps),
         run (inferIdentity simple_recursion) (S_Rec $ S_Sel1 $ S_Var $ S_Sel2 $ S_Sel1 $ S_Weaken S_Eps)]

test = run (normalize (inferIdentity extra_r_and_wk_after)) (S_Rec $ S_Sel1 $ S_Var $ S_Sel2 $ S_Sel1 $ S_Weaken S_Eps)