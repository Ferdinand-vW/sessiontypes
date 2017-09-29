{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

import Control.SessionTypes
import Control.SessionTypes.Visualize
import Data.Proxy (Proxy (..))


-- This test requires visual verification.
-- Run the following to generate a diagram:
-- > stack build
-- > stack exec test-visualizer -- -o output.svg -w 600 -h 600
-- Adjust the height and width if necessary
main = visualizeP p

p :: Proxy (R ( Int :!> Sel '[ Bool :?> Off [Wk Eps, V], R (Sel '[Char :!> V, Wk V])]))
p = Proxy