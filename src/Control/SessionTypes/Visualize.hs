{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE ConstraintKinds           #-}
-- | This module defines an interpreter for visualizing session types.
--
-- Using `visualize` or `visualizeP` you can create a diagram that displays a session type using a set of nodes and arrows that connect these nodes.
module Control.SessionTypes.Visualize (
  visualize,
  visualizeP,
  MkDiagram
) where

import           Control.SessionTypes.MonadSession
import           Control.SessionTypes.Types           as ST

import           Diagrams.Prelude hiding (Coordinates, loc)
import           Diagrams.Backend.SVG.CmdLine
import           Control.Monad.State
import qualified Data.Vector                  as V
import           Data.Proxy (Proxy (..))
import           Data.Typeable (Typeable, typeRep)

-- | Visualizes the session type of a given `STTerm`
-- You may use this function in the following way
--
-- > main = visualize st
--
-- Then the following command will generate a diagram named "sessiontype.png" 
--
-- > stack exec vis-sessiontype -- -o sessiontype.png -w 400
--
-- For more information on how to generate a diagram please visit the 
-- <https://hackage.haskell.org/package/diagrams diagrams> package
visualize :: forall m ctx s r a. (MonadSession m, MkDiagram s) => m ('Cap ctx s) r a -> IO ()
visualize _ = mainWith $ mkDiagram (Proxy :: Proxy s)

-- | Visualizes a given session type denoted by a Proxy.
visualizeP :: MkDiagram s => Proxy s -> IO ()
visualizeP p = mainWith $ mkDiagram p




-- We define a grid as a vector of vectors of nodes
type Grid = V.Vector (V.Vector Node)

newGrid :: Int -> Int -> Grid
newGrid x y = V.map (\_ -> V.replicate (x + 1) empNode) $ V.replicate (y + 1) V.empty

gridIndex :: Grid -> (Int, Int) -> Maybe Node
gridIndex g (x,y) = g V.!? y >>= \v -> v V.!? x

gridIndex' :: Grid -> (Int, Int) -> Node
gridIndex' g (x,y) = g V.! y V.! x

-- We define a data type to represent Nodes
-- Nodes are named such that later on we can place arrows between them
-- They also have a type, which is necessary to determine whether an arrow should be placed
-- Each node must also have a Diagram representation
data Node = Node {name :: String, nodeType :: NodeType, nodeDiag :: Diagram B }
-- The different node types
data NodeType = N_Send | N_Recv | N_B | N_Anch | N_CR | N_End | N_Emp | T | N_R | N_V | N_W deriving (Eq, Show)

data Orientation = Horizontal | Vertical

------------ Basic Diagrams

diagSize :: Double
diagSize = 1

newDiag :: String -> Diagram B
newDiag s = (text s <> circle diagSize) # fontSize (local diagSize)

pointDiag :: Diagram B
pointDiag = circle 0.01 # lw none

arrBetween_noHead :: String -> String -> Diagram B -> Diagram B
arrBetween_noHead s1 s2 d = (connectOutside' (with & arrowHead .~ noHead )) s1 s2 d

----------- Node for each session type

sendNode, recvNode, endNode, empNode, crNode, anchNode, offNode, selNode, rNode, vNode, wNode :: Node
sendNode  = Node ""     N_Send  $ newDiag ":!>"
recvNode  = Node ""     N_Recv  $ newDiag ":?>"
endNode   = Node "end"  N_End   $ newDiag "End"
empNode   = Node ""     N_Emp   $ newDiag "" # lw none
crNode    = Node ""     N_CR    $ pointDiag
anchNode  = Node ""     N_Anch  $ pointDiag
offNode   = Node ""     N_B     $ newDiag "Off"
selNode   = Node ""     N_B     $ newDiag "Sel"
rNode     = Node ""     N_R     $ newDiag "R"
vNode     = Node ""     N_V     $ newDiag "V"
wNode     = Node ""     N_W     $ newDiag "Wk"

----------- Other node types

encase :: Node -> Node
encase (Node n nt d) = Node n nt (d <> (circle diagSize # lw none))

typeBox :: String -> Node
typeBox s = Node "" T $ newDiag s # lw none

{-

    DIAGRAM API

-}

-- When building the diagram we will need to keep track of several things
data DState = DState { 
  counter :: Int, -- ^ Used to make unique name
  weakenN :: Int, -- ^ Number of weakenings
  loc :: (Int, Int), -- ^ current position in the grid
  diag :: Diagram B, -- ^ Diagram that we build
  grid :: Grid -- ^ Grid that will contain nodes 
  }


newDState :: Grid -> DState
newDState = DState 0 0 (0,0) mempty

-- | We use a State monad to modify the diagram
type DiagramM a = StateT DState IO a

runDiagramM :: DState -> DiagramM a -> IO (a, DState)
runDiagramM state m = runStateT m state

-- Creates a Diagram from a given grid
gridToDiagram :: Grid -> Diagram B
gridToDiagram g = vsep (2 * diagSize) $ V.toList $ V.map (hsep (2 * diagSize) . map nodeDiag . V.toList) g

-- | Returns a unique name
newName :: DiagramM String
newName = do
  (DState n w xy d g) <- get
  put (DState (n + 1) w xy d g)
  return $ show n

-- | Name a given node
nameNode :: Node -> DiagramM Node
nameNode (Node _ t d) = do
  name <- newName
  return $ Node name t $ d # named name

-- | Checks the current position and returns the name of the node
getNameAtCurr :: DiagramM String
getNameAtCurr = do
  loc <- getLoc
  grid <- getGrid
  let (Node name _ _) = gridIndex' grid loc
  return name

-- | Returns current location
getLoc :: DiagramM (Int, Int)
getLoc = fmap loc get

-- | Update the current location with a new location
saveLoc :: (Int, Int) -> DiagramM ()
saveLoc (x,y) = modify $ \(DState n w _ d g) -> DState n w (x,y) d g

-- | Move up by one
incrLocY :: DiagramM ()
incrLocY = modify $ \(DState n w (x,y) d g) -> DState n w (x, y + 1) d g

-- | Move down by one
decrLocY :: DiagramM ()
decrLocY = modify $ \(DState n w (x,y) d g) -> DState n w (x, y - 1) d g

-- | Move to the right by one
incrLocX :: DiagramM ()
incrLocX = modify $ \(DState n w (x,y) d g) -> DState n w (x + 1, y) d g

-- | Keep moving to the right until
incrLocXWhile :: (Node -> Bool) -> DiagramM ()
incrLocXWhile f = do
  incrLocX
  loc <- getLoc
  grid <- getGrid
  let mn = gridIndex grid loc
  case mn of
    Nothing -> return ()
    Just n | f n -> incrLocXWhile f
           | otherwise -> return ()

-- | Increase the number of weakenings
incrWk :: DiagramM ()
incrWk = modify $ \(DState n w loc d g) -> DState n (w + 1) loc d g

-- | decrease the number of weakenings
decrWk :: DiagramM ()
decrWk = modify $ \(DState n w loc d g) -> DState n (w - 1) loc d g

-- | Get current number of weakenings
getWk :: DiagramM Int
getWk = fmap weakenN get

-- | Insert new number of weaknings into state
saveWk :: Int -> DiagramM ()
saveWk w = modify $ \(DState n _ loc d g) -> DState n w loc d g

-- | Returns the grid
getGrid :: DiagramM Grid
getGrid = fmap grid get

-- | Saves a new grid
saveGrid :: Grid -> DiagramM ()
saveGrid g = modify $ \(DState n w loc d _) -> DState n w loc d g

-- | Returns the diagram
getDiag :: DiagramM (Diagram B)
getDiag = fmap diag get

-- | Saves a new diagram
saveDiag :: Diagram B -> DiagramM ()
saveDiag d = modify $ \(DState n w loc _ g) -> DState n w loc d g

-- | Place a node at the current location
placeAtCurrM :: Node -> DiagramM ()
placeAtCurrM sn = do
  loc <- getLoc
  placeAtLocM sn loc

-- | Place a node at the given location
placeAtLocM :: Node -> (Int, Int) -> DiagramM ()
placeAtLocM sn loc = do
  grid <- getGrid
  saveGrid $ placeAtLoc sn loc grid

placeAtLoc :: Node -> (Int, Int) -> Grid -> Grid
placeAtLoc sn (x,y) grid = grid V.// [(y, (grid V.! y) V.// [(x, sn)])]

-- Internal utility function
printGrid :: Grid -> IO ()
printGrid g = forM_ g $ \hv -> do
  forM_ hv (\(Node n t _) -> putStr (show (n, t) ++ " "))
  putStrLn ""

{-
We use a grid to give a visualization of session types. The grid contains nodes
and is sized by the maximum number of nodes in the X and Y dimension.
The size is calculated using the `Coordinates` type class.

The grid is initially filled with so called empty nodes that don't show in the generated diagram.
We will first use the type class `PlaceNodes` to place nodes in the grid that describe the session type.
Initially we start at location (0,0), which is the left top in the diagram. Then the `PlaceNodes` will independently
for each partial session type place nodes. After having done so it will update the position that we are at and do a recursive call
for the second part of the session type if it exists.

We'll shortly describe how nodes are placed for each session type:
  a :!> r : Places two nodes. First a node describing `a` at the current position.
            Then a new node describing the operator `:!>` at 1 position below it.
            The y coordinate of the position is then once more increased before making a recursive call on `r`.
  
  a :?> r : Similar to `a :!> r`

  Sel '[s] : For each branching session ype we have to write two instances. In this case we only have to make a recursive call on `s`

  Sel (s ': t ': xs): We place a node describing `Sel` at the current position. We then increment y and do a recursive call on `s`, such that
                      the first branch is placed directly below `Sel`. After completion of the recursive call we go back to our original position
                      and move in the X-dimension equal to the size of `s` in its X-dimension + 1. This is necessary to avoid overlap between the two
                      branches. In our new position we place a so called corner node that is essentially invisible, but is necessary for arrows.
                      Finally we increment y and do a recursive call on `Sel (t ': xs)`.
  
  Off '[s] : Same as `Sel '[s]`

  Off (s ': t ': xs) : Similar to `Sel (s ': t ': xs)`.

  R s : We place a node describing `R` and replace all empty nodes to the right of this node with an anchor node. The anchor node is necessary for a `V` node
        to connect with this `R` node. Since there can be multiple `V` nodes, we might need more than one anchor. One solution is to calculate exactly at which 
        X-coordinate these `V` nodes are and use these coordinates to place anchor nodes. An easier solution is to simply place anchor nodes at every empty node
        to the right of this `R` node, since anchor nodes in most cases can be treated as empty nodes. So if one overlaps with a branch, then it will be removed
        by that branch. After having placed these anchor nodes we do a recursive call on `s`.

  Wk s : Similar to `R`, but without the anchor nodes.

  V : Places two nodes. One at the current position describing `V` and an anchor node directly to the right. This anchor node will connect to an anchor node
      placed right to a `R` node.

  Eps : A single node describing `Eps`.
                     

After all nodes have been placed we will have to connect them.
We will walk the grid starting from (0,0).
Depending on the type of the node we know which session type it is describing.
And as described above, we know exactly where the next nodes are.
Connecting two nodes using the Diagrams library is done by taking two named diagrams (nodes)
and constructing a single diagram that contains both nodes with an arrow between them.

For both branching and recursion we have to take a bit more care about how we connect nodes with arrows.
The corner node of a branching is not directly to the right of the branching node, so we have to walk over all empty
and anchor nodes until it finds one.
With recursion we need to consider the number of `R` and `Wk` nodes that we have passed before connecting a `V` node to a `R` node.
Once that number is known 3 arrows will be placed: from the `V` node to its anchor node, from that anchor node to an anchor of a `R` node and from that anchor
to that `R` node. 


-}

-- | Necessary type constraints for making a diagram 
type MkDiagram s = (Coordinates s, PlaceNodes s)

-- | Makes a diagram for a given session type
mkDiagram :: MkDiagram s => Proxy s -> IO (Diagram B)
mkDiagram p = do
  -- place nodes in the grid
  dstate <- dstateWNodesIO
  -- connect the grid and build a Diagram
  (diag, DState n _ _ d g) <- runStateT connectGrid dstate
  -- Place arrows going from a `V` to a `R`
  fmap fst $ runStateT connectRecursions (DState n 0 (0,0) diag g)
  where
    dstateWNodesIO = fmap snd $ runStateT (placeNodes p) (newDState $ newGrid (getX p) (getY p))

-- | Determines size of grid based on the session types
class Coordinates (s :: ST k) where
  getX :: Proxy s -> Int
  getY :: Proxy s -> Int

instance Coordinates r => Coordinates (a :!> r) where
  getY Proxy = 2 + getY (Proxy :: Proxy r)
  getX Proxy = getX (Proxy :: Proxy r)

instance Coordinates r => Coordinates (a :?> r) where
  getY Proxy = 2 + getY (Proxy :: Proxy r)
  getX Proxy = getX (Proxy :: Proxy r)

instance Coordinates t => Coordinates (Sel '[t]) where
  getY Proxy = getY (Proxy :: Proxy t)
  getX Proxy = getX (Proxy :: Proxy t)

instance (Coordinates s, Coordinates (Sel (t ': xs))) => Coordinates (Sel (s ': t ': xs)) where
  getY Proxy = 1 + getY (Proxy :: Proxy s) `max` getY (Proxy :: Proxy (Sel (t ': xs)))
  getX Proxy = 1 + getX (Proxy :: Proxy s) + getX (Proxy :: Proxy (Sel (t ': xs)))

instance Coordinates t => Coordinates (Off '[t]) where
  getY Proxy = getY (Proxy :: Proxy t)
  getX Proxy = getX (Proxy :: Proxy t)

instance (Coordinates s, Coordinates (Off (t ': xs))) => Coordinates (Off (s ': t ': xs)) where
  getY Proxy = 1 + getY (Proxy :: Proxy s) `max` getY (Proxy :: Proxy (Off (t ': xs)))
  getX Proxy = 1 + getX (Proxy :: Proxy s) + getX (Proxy :: Proxy (Off (t ': xs)))

instance Coordinates s => Coordinates (R s) where
  getY _ = 1 + getY (Proxy :: Proxy s)
  getX _ = getX (Proxy :: Proxy s)

instance Coordinates ST.V where
  getY _ = 0
  getX _ = 1

instance Coordinates s => Coordinates (Wk s) where
  getY _ = 1 + getY (Proxy :: Proxy s)
  getX _ = getX (Proxy :: Proxy s)

instance Coordinates 'Eps where
  getY _ = 0
  getX _ = 0


-- | Type class that places the nodes at the correct locations in the grid
class PlaceNodes (s :: ST k) where
  placeNodes :: Proxy s -> DiagramM ()

instance (Typeable a, PlaceNodes r) => PlaceNodes (a :!> r) where
  placeNodes Proxy = operationDiagram sendNode (Proxy :: Proxy a) (Proxy :: Proxy r)

instance (Typeable a, PlaceNodes r) => PlaceNodes (a :?> r) where
  placeNodes Proxy = operationDiagram recvNode (Proxy :: Proxy a) (Proxy :: Proxy r)

instance PlaceNodes s => PlaceNodes (Sel '[s]) where
  placeNodes _ = placeNodes (Proxy :: Proxy s)

instance (Coordinates s, PlaceNodes s, PlaceNodes (Sel (t ': xs))) => PlaceNodes (Sel (s ': t ': xs)) where
  placeNodes _ = branchDiagram selNode (Proxy :: Proxy s) (Proxy :: Proxy (Sel (t ': xs)))
    
instance PlaceNodes s => PlaceNodes (Off '[s]) where
  placeNodes _ = placeNodes (Proxy :: Proxy s)

instance (Coordinates s, PlaceNodes s, PlaceNodes (Off (t ': xs))) => PlaceNodes (Off (s ': t ': xs)) where
  placeNodes _ = branchDiagram offNode (Proxy :: Proxy s) (Proxy :: Proxy (Off (t ': xs)))

instance PlaceNodes s => PlaceNodes (R s) where
  placeNodes p = do
    -- create a recursion node
    rnode' <- nameNode rNode
    loc <- getLoc

    -- place the node at the current location
    placeAtCurrM rnode'
    incrLocY

    -- do a recursive call for the other nodes
    placeNodes (Proxy :: Proxy s)

    -- place an anchor node
    saveLoc loc
    incrLocX
    placeAnchors (\(x,y) -> (x + 1, y))

instance PlaceNodes ST.V where
  placeNodes _ = do
    -- create a recursion variable node
    -- and place it at the current loc
    vnode <- nameNode vNode
    placeAtCurrM vnode

    -- Place an anchor node
    incrLocX
    anchnode <- nameNode anchNode
    placeAtCurrM $ encase anchnode

instance PlaceNodes s => PlaceNodes (Wk s) where
  placeNodes _ = do
    wnode <- nameNode wNode

    placeAtCurrM wnode
    incrLocY

    placeNodes (Proxy :: Proxy s)

instance PlaceNodes 'Eps where
  placeNodes Proxy = do
    end <- nameNode endNode

    placeAtCurrM end
    return ()

-- Places the nodes for the send and receive session type
operationDiagram :: (Typeable a, PlaceNodes r) => Node -> Proxy a -> Proxy r -> DiagramM ()
operationDiagram node pr1 pr2 = do
  tb <- nameNode $ typeBox $ show $ typeRep pr1
  nnode <- nameNode node

  placeAtCurrM tb
  incrLocY
  placeAtCurrM nnode 
  incrLocY

  placeNodes pr2

-- Places the nodes for the branching session types
branchDiagram :: (Coordinates s, PlaceNodes s, PlaceNodes r) => Node -> Proxy s -> Proxy r -> DiagramM ()
branchDiagram n pr1 pr2 = do
  br <- nameNode n
  cr <- nameNode crNode

  placeAtCurrM br
  (x,y) <- getLoc
  incrLocY

  placeNodes pr1
  saveLoc (x + getX pr1 + 1, y)
  placeAtCurrM (encase cr)
  incrLocY

  placeNodes pr2


-- Walks the grid in a given direction and replaces
-- all empty nodes with an anchor node
placeAnchors :: ((Int, Int) -> (Int, Int)) -> DiagramM ()
placeAnchors move = do
  loc <- getLoc
  g <- getGrid
  let mn = gridIndex g loc -- get the node at the current position
  case mn of
    -- We are out of bounds so we stop recursion
    Nothing -> return ()
    -- If empty node then replace it with a anchor
    Just n | nodeType n == N_Emp -> do
      nn <- nameNode anchNode
      placeAtCurrM (encase nn)
      -- move and do a recursive call
      saveLoc (move loc)
      placeAnchors move
           | otherwise -> return ()


-- Top level function for placing arrows between nodes
-- returns a Diagram that can be displayed
connectGrid :: DiagramM (Diagram B)
connectGrid = do
  grid <- getGrid
  -- take the grid and turn it into diagram
  -- the diagram contains the nodes, but does not contain arrows
  addConn $ gridToDiagram grid
  where
    addConn d = do
      grid <- getGrid
      -- Takes the existing diagram and will add arrows to this diagram
      walkGrid (0,0) connectNodes grid d

-- Implements the logic for connecting two nodes
-- If two nodes are to be connected we add a property on the 
-- diagram that adds an arrow between the nodes
connectNodes :: Node -> Node -> Orientation -> Diagram B -> DiagramM (Diagram B)
connectNodes (Node n1 t1 d1) (Node n2 t2 d2) Horizontal d
  | t1 == N_B && t2 == N_CR = return $ (d # arrBetween_noHead n1 n2)
  | otherwise = return d
connectNodes (Node n1 t1 _) (Node n2 t2 _) Vertical d
  | t2 /= N_CR
  && t1 /= N_Emp = return $ d # connectOutside n1 n2
  | otherwise = return d

-- Walkes the grid starting at the given location.
-- It also takes a function that can connect two nodes, the grid and the diagram that is to be built upon
-- The function works by taking the current position and walking downwards to see if there are any nodes
-- If there are it will use the function to place any arrows and then do a recursive call downwards
-- Otherwise it will return the diagram built so far and tries the same from the original position in a rightward movement
-- This function is primarily for walking over the grid, whereas the given function implements the logic for adding arrows
walkGrid :: (Int, Int) -> (Node -> Node -> Orientation -> Diagram B -> DiagramM (Diagram B)) -> Grid -> Diagram B -> DiagramM (Diagram B)
walkGrid (x,y) f g d = tryVertical d >>= tryHorizontal (x,y)
    where
      currNode = gridIndex' g (x,y) -- current node
      tryHorizontal (x',y') d = do
        case gridIndex g (x' + 1,y') of
          Nothing -> return d -- out of bounds
          -- If its an anchor or empty node there is nothing to connect, but there might be a corner node further to the right
          -- We don't do a recursive call on walkGrid, because that would try to connect an empty/anchor node to anything below it
          Just sn | nodeType sn == N_Anch || nodeType sn == N_Emp -> tryHorizontal (x' + 1, y) d
          -- If we found a corner node we use `f` to add any arrows.
          -- We can now also stop looking to the right, so we call walkGrid again
                  | nodeType sn == N_CR -> do
                    d' <- f currNode sn Horizontal d
                    walkGrid (x' + 1, y') f g d'
                  | otherwise -> return d 
      -- Vertical movement is much more simple, either there is a node directly below it or there will never be any
      tryVertical d = case gridIndex g (x, y + 1) of
        Nothing -> return d
        Just sn -> do
          d' <- f currNode sn Vertical d
          walkGrid (x, y + 1) f g d'

-- Adds arrows going from V to an R
-- We traverse the grid and upon encountering a V we have to do backtracking 
-- to find the corresponding R
connectRecursions :: DiagramM (Diagram B)
connectRecursions = do
  pos <- getLoc
  grid <- getGrid
  let (Node name nt _) = gridIndex' grid pos
  case nt of
    N_V -> do
      -- We move to the anchor node and start backtracking
      incrLocX
      backTrack name
      getDiag
    N_B -> do
      incrLocY
      d <- connectRecursions

      saveDiag d
      saveLoc pos
      -- Look for second branch
      incrLocXWhile (\(Node _ nt _) -> nt /= N_CR)
      connectRecursions
    N_W -> do
      incrLocY
      -- increment number of weakens we found
      incrWk
      wk <- getWk
      connectRecursions
      -- ensure that weakenings in one branch don't affect other branches
      decrWk
      getDiag
    N_End -> getDiag
    _ -> do
      incrLocY
      connectRecursions

-- The backtrack function starts at the anchor node of a `V` node
-- It starts moving upwards. After every increment it will look 
-- for `R` nodes to its left
-- If there exists one, then if the number of weakenings is at 0 we make an arrow
-- to its anchor node and from its anchor node to the `R` node itself.
-- If the number of weakens is higher than zero, then we keep moving upward 
-- while decrementing the number of weakenings.
-- if there is no `R` node then we also move upwards
backTrack :: String -> DiagramM ()
backTrack name = do
  grid <- getGrid

  pos <- getLoc
  cname <- getNameAtCurr
  goUp cname -- need the name of the original anchor node to make a connection
  saveLoc pos
  where
    goUp cname = do
      ms <- rToLeft -- Looks for `R` node to the left
      case ms of
        -- If there is none we move upward
        Nothing -> do
          decrLocY
          goUp cname
        Just rname -> do
          wkC <- getWk
          if wkC == 0 -- we can make a connection
            then do
              cname' <- getNameAtCurr
              d <- getDiag
              saveDiag (d # arrBetween_noHead name cname
                          # arrBetween_noHead cname cname'
                          # connectOutside cname' rname)
            else do -- decrement the number of weakenings and move upwards
              decrWk
              decrLocY
              goUp cname
              saveWk wkC

-- Looks for a `R` node to the left of the current location
rToLeft :: DiagramM (Maybe String)
rToLeft = do
  (x,y) <- getLoc
  grid <- getGrid
  let mnode = gridIndex grid (x,y)
  mn <- case mnode of
    Nothing -> return Nothing
    Just (Node name nt _) 
      | nt == N_R -> return $ Just name -- found one
      | nt == N_Anch || nt == N_Emp -> do -- keep moving left
        saveLoc (x-1, y)
        ms <- rToLeft
        return ms
      | otherwise -> return Nothing -- could not find any

  saveLoc (x, y) -- set position back to original location
  return mn