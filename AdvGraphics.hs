-- Application of animating DFS, Dijkstra's Shortest Paths and Kruskal's MST algorithms
-- This application is belong to Junyang Xin's final year project "Haskell Development of Graph Algorithms"
-- Author: Junyang Xin (xinjunyang@gmail.com)
-- Supervisor: Richard Lawlor (richard.lawlor@comp.dit.ie)
-- Copyright@ Junyang Xin, Richard Lawlor and Dublin Institute of Technology

module Main where
import SOE hiding (Region)
import Picture
import Draw
import Array


-- shape of vertex
-- written by: Junyang Xin
node = Shape (Ellipse 0.23 0.23)

type Myvertex = (Float, Float)

-- list of positions on the plane for vertices
-- can add new coordinates into the list when there are more vertices than in the graph than the current number of 12
-- written by: Junyang Xin
locations :: [Myvertex]
locations = [(-3.5, 0), (-2.5, -1.5), (-1.5, 0), (-2.5, 1.5), (-0.5, -1.5),
			 (0.5, 0), (-0.5, 1.5), (1.5, -1.5), (1.5, 1.5), (2.5, 0),
			 (-1.5, -2.5), (0.5, -2.5), (2.5, -2.5),(-1.5, 2.5), (0.5, 2.5),
			 (2.5, 2.5), (3.5, 1.5), (3.5, -1.5), (3.5, 0)]

-- data structure of graph: adjacent list
type Graph n w = Array n [(n, w)]

-- function to create a graph with three parameters
-- dir:	if a graph is directed or undirected
-- bnds: lower and upper boundaries of the graph
-- es: list of edges of the graph
-- function is from book "Algorithms: A Functional Programming Approach"
mkGraph :: (Ix n, Num w) => Bool -> (n, n) -> [(n, n, w)] -> Graph n w
mkGraph dir bnds es =
    accumArray (\xs x -> x:xs) [] bnds
	       ([(x1, (x2, w)) | (x1, x2, w) <- es] ++
		if dir then []
		else [(x2, (x1, w)) | (x1, x2, w) <- es, x1 /= x2])

-- function to retrieve the adjacent vertices of a vertex in a graph
-- function is from book "Algorithms: A Functional Programming Approach"
adjacent :: (Ix n, Num w) => (Graph n w) -> n -> [n]
adjacent g v = map fst (g!v)

-- function to retrieve all the nodes of a graph
-- function is from book "Algorithms: A Functional Programming Approach"
graphNodes :: (Ix n, Num w) => (Graph n w) -> [n]
graphNodes g = indices g

-- function to detect if an edge is in a graph or not
-- function is from book "Algorithms: A Functional Programming Approach"
edgeIn :: (Ix n, Num w) =>  (Graph n w) -> (n, n) -> Bool
edgeIn g (x, y) = elem y (adjacent g x)

-- function to retrieve the weight of an edge with the start and target vertices given
-- function is from book "Algorithms: A Functional Programming Approach"
weight :: (Ix n, Num w) => n -> n -> (Graph n w) -> w
weight x y g = head [c | (a, c) <- g!x, (a == y)]

-- function to retrieve all the edges of a directed graph
-- function is from book "Algorithms: A Functional Programming Approach"
edgesD :: (Ix n, Num w) => (Graph n w) -> [(n, n, w)]
edgesD g = [(v1, v2, w) | v1 <- graphNodes g, (v2, w) <- g!v1]

-- function to retrieve all the edges of a undirected graph
-- function is from book "Algorithms: A Functional Programming Approach"
edgesU :: (Ix n, Num w) => (Graph n w) -> [(n, n, w)]
edgesU g = [(v1, v2, w) | v1 <- graphNodes g, (v2, w) <- g!v1, v1 < v2]

-- depth-first search returning a list of nodes of a graph in the order of being visited
-- function is from book "Algorithms: A Functional Programming Approach"
depthFirstSearch :: (Ix a, Num w) => a -> (Graph a w) -> [a]
depthFirstSearch start g = reverse (dfs [start] [])
  where 
    dfs [] vis = vis
    dfs (c:cs) vis
	| elem c vis = dfs cs vis
	| otherwise  = dfs ((adjacent g c) ++ cs) (c:vis)

-- function to get the intermediate optional edges of vertices during the search
-- written by: Junyang Xin
getDepthFirstItmOptions :: (Ix n, Num w) => Graph n w -> [n] -> [n] -> [n] -> [[n]] -> [[n]]
getDepthFirstItmOptions graph [] (y:ys) vis options = reverse options
getDepthFirstItmOptions graph (x:xs) (y:ys) vis options
	= getDepthFirstItmOptions graph xs ys (y:vis) ((removeVisited (y:vis) (adjacent graph x)):options)
		where 
			removeVisited visitedVertices [] = []
			removeVisited visitedVertices (adjVertex:avs)
				| elem adjVertex visitedVertices = removeVisited visitedVertices avs
				| otherwise						 = adjVertex : (removeVisited visitedVertices avs)

-- function to animate depth-first search algorithm
-- written by: Junyang Xin
animateDepthFirstSearch graph window [] _ _ _ = []
animateDepthFirstSearch graph window vs [] _ vertexCord = [(makeSequence [(drawOutVertex window Green (makeVertexToDraw (vertexCord!(last vs)))), (drawOutVertexId window Black (makeVertexIdToDraw (last vs) (vertexCord!(last vs))))])]
animateDepthFirstSearch graph window vs _ [] vertexCord = [(makeSequence [(drawOutVertex window Green (makeVertexToDraw (vertexCord!(last vs)))), (drawOutVertexId window Black (makeVertexIdToDraw (last vs) (vertexCord!(last vs))))])]
animateDepthFirstSearch graph window (v:vs)	(o:os) (e:es) vertexCord
	 = drawVertexAndId : drawOptionalEdges : drawDepthFirstEdge : animateDepthFirstSearch graph window vs os es vertexCord
		where
			drawVertexAndId = (makeSequence [(drawOutVertex window Green (makeVertexToDraw (vertexCord!v))), (drawOutVertexId window Black (makeVertexIdToDraw v (vertexCord!v)))])
			drawOptionalEdges = (makeSequence (drawOutEdges window Red (makeEdgesToDraw (setEdgeLocation vertexCord (makeEdges (fst e) o)))))
			drawDepthFirstEdge = (makeSequence ([drawInWindow window (withColor Green (polyline (map trans [vertexCord!(fst e), vertexCord!(snd e)])))] ++ [drawInWindow window (withColor Green (polyline (map trans [vertexCord!(fst e), vertexCord!(snd e)])))]))

-- animating depth-first search algorithm on directed graph
-- written by: Junyang Xin
mainDepthFirstSearchDirected = runGraphics $
	do src <- readFile "DfsDirected.txt"		-- reading the graph information from a file
	   let edges = map (split.words) (tail (lines src))		-- parsing the text of the file
	       maxBound = read (head (lines src))	-- get the upper bound of the graph (the number of vertices)
	   -- start point of the algorithm
	       origin = 1
	   -- create a directed graph
	       graph = mkGraph True (1, maxBound) edges
	   -- ids of vertices 
	       vertexIds = graphNodes graph
	   -- list of vertex ids and the corresponding positions
	       positionsAndIds = zip locations vertexIds
	   -- create an array of coordinations of the vertices for convinient use
	       vertexCord = array (1, maxBound) [(index, (x, y)) | ((x, y), index) <- positionsAndIds]
	   -- edges represented by two coordinations of start vertex and target vertex
	       edgesOfVertices = [(vertexCord!start, vertexCord!end) | (start, end, weight) <- edges]
	   -- vertices to draw
	       vertexToDraw = [Translate (x, y) node | (x, y) <- (take maxBound locations)]
	   -- edges represented by polyline to draw
	       edgesToDraw = [polyline (map trans [start, end]) | (start, end) <- edgesOfVertices]
	   -- vertex ids to draw
	       vertexIdsToDraw = [text (trans (x-0.08, y+0.08)) (show z) | ((x, y), z) <- positionsAndIds]
	   -- positions of weights to draw
	       positionOfWeights = [((calculateMidCord (vertexCord!start) (vertexCord!end)), weight) | (start, end, weight) <- edges]
	   -- weights to draw
	       weightsToDraw = [text (trans (x, y)) (show z) | ((x, y), z) <- positionOfWeights] 
	   w <- openWindow "DFS Directed Graph" (800, 650)
	   drawInWindow w (withColor White (polygon [(0,0), (799,0), (799,649), (0,649)]))
	   -- actions to animate the Dijkstra's algorithm
	   let 
		   -- list of nodes in the order of being visited during the depth-first search
		   depthFirstSearchVertices = depthFirstSearch origin graph
		   -- list of optinal edges at during the depth-first search
		   depthFirstSearchOptionalEdges = getDepthFirstItmOptions graph (tail (map fst (newDepthFirstSearch origin graph))) (depthFirstSearch origin graph) [] []
		   -- list of edges being taken during the depth-first search
		   depthFirstSearchEdges = tail (newDepthFirstSearch origin graph)
		   -- list of drawing actions of animating depth-first search
		   animateAlgorithmDraw = animateDepthFirstSearch graph w depthFirstSearchVertices depthFirstSearchOptionalEdges depthFirstSearchEdges vertexCord
		   -- actions of waiting user to press a key on the keyboard
		   userInteraction = map (change (getKey w)) animateAlgorithmDraw
		   userInteractionList = [(sequence_ [action]) | action <- userInteraction]
	   let 
		   arrowPositions = map calPosition edgesOfVertices
		   arrowsToDraw = [polygon (map trans position) | position <- arrowPositions]		   
	   -- mix the animating actions and the user interaction actions
	   let drawWithInteraction = mixList userInteractionList animateAlgorithmDraw
	   -- draw out the vertices
	   sequence_ [drawRegionInWindow w Red n | n <- vertexToDraw]
	   -- draw out the edges
	   sequence_ [drawInWindow w (withColor Yellow e) | e <- edgesToDraw]
	   -- draw out the vertex ids
	   sequence_ [drawInWindow w (withColor Black t) | t <- vertexIdsToDraw]
	   -- draw out the weights
	   sequence_ [drawInWindow w (withColor Black t) | t <- weightsToDraw]
	   -- arrows to draw	   
	   sequence_ [drawInWindow w (withColor Black arrow) | arrow <- arrowsToDraw]
	   sequence_ drawWithInteraction
	   spaceClose w
	   where
			-- function to parse the information of graph in a file
			split [start, end, weight] = ((read start), (read end), (read weight))
-- animating depth-first search algorithm on undirected graph
-- written by: Junyang Xin			
mainDepthFirstSearchUndirected = runGraphics $
	do src <- readFile "DfsUndirected.txt"		-- reading the graph information from a file
	   let edges = map (split.words) (tail (lines src))		-- parsing the text of the file
	       maxBound = read (head (lines src))	-- get the upper bound of the graph (the number of vertices)
	   -- start point of the algorithm
	       origin = 1
	   -- create a directed graph
	       graph = mkGraph False (1, maxBound) edges
	   -- ids of vertices 
	       vertexIds = graphNodes graph
	   -- list of vertex ids and the corresponding positions
	       positionsAndIds = zip locations vertexIds
	   -- create an array of coordinations of the vertices for convinient use
	       vertexCord = array (1, maxBound) [(index, (x, y)) | ((x, y), index) <- positionsAndIds]
	   -- edges represented by two coordinations of start vertex and target vertex
	       edgesOfVertices = [(vertexCord!start, vertexCord!end) | (start, end, weight) <- edges]
	   -- vertices to draw
	       vertexToDraw = [Translate (x, y) node | (x, y) <- (take maxBound locations)]
	   -- edges represented by polyline to draw
	       edgesToDraw = [polyline (map trans [start, end]) | (start, end) <- edgesOfVertices]
	   -- vertex ids to draw
	       vertexIdsToDraw = [text (trans (x-0.08, y+0.08)) (show z) | ((x, y), z) <- positionsAndIds]
	   -- positions of weights to draw
	       positionOfWeights = [((calculateMidCord (vertexCord!start) (vertexCord!end)), weight) | (start, end, weight) <- edges]
	   -- weights to draw
	       weightsToDraw = [text (trans (x, y)) (show z) | ((x, y), z) <- positionOfWeights] 
	   w <- openWindow "DFS Undirected Graph" (800, 650)
	   drawInWindow w (withColor White (polygon [(0,0), (799,0), (799,649), (0,649)]))
	   -- actions to animate the Dijkstra's algorithm
	   let 
		   -- list of nodes in the order of being visited during the depth-first search
		   depthFirstSearchVertices = depthFirstSearch origin graph
		   -- list of optinal edges at during the depth-first search
		   depthFirstSearchOptionalEdges = getDepthFirstItmOptions graph (tail (map fst (newDepthFirstSearch origin graph))) (depthFirstSearch origin graph) [] []
		   -- list of edges being taken during the depth-first search
		   depthFirstSearchEdges = tail (newDepthFirstSearch origin graph)
		   -- list of drawing actions of animating depth-first search
		   animateAlgorithmDraw = animateDepthFirstSearch graph w depthFirstSearchVertices depthFirstSearchOptionalEdges depthFirstSearchEdges vertexCord
		   -- actions of waiting user to press a key on the keyboard
		   userInteraction = map (change (getKey w)) animateAlgorithmDraw
		   userInteractionList = [(sequence_ [action]) | action <- userInteraction]
	   -- mix the animating actions and the user interaction actions
	   let drawWithInteraction = mixList userInteractionList animateAlgorithmDraw
	   -- draw out the vertices
	   sequence_ [drawRegionInWindow w Red n | n <- vertexToDraw]
	   -- draw out the edges
	   sequence_ [drawInWindow w (withColor Yellow e) | e <- edgesToDraw]
	   -- draw out the vertex ids
	   sequence_ [drawInWindow w (withColor Black t) | t <- vertexIdsToDraw]
	   -- draw out the weights
	   sequence_ [drawInWindow w (withColor Black t) | t <- weightsToDraw]
	   sequence_ drawWithInteraction
	   spaceClose w
	   where
			-- function to parse the information of graph in a file
			split [start, end, weight] = ((read start), (read end), (read weight))			
			
-- edges of sample graph
orgEdges = [(1, 2, 10), (1, 3, 20), (1, 4, 15),
	    (2, 6, 24),
	    (3, 6, 16), (3, 7, 30),
	    (4, 5, 35),
	    (5, 6, 25), (5, 8, 35),
	    (6, 8, 21),
	    (7, 8, 17)]

-- sample undirected graph created from the sample edges
-- written by: Junyang Xin
graph1 = mkGraph False (1, 8) orgEdges

-- sample directed graph created from the sample edges
-- written by: Junyang Xin
graph2 = mkGraph True (1, 8) orgEdges

-- function to mix the items from two list in the alternating order
-- written by: Junyang Xin
mixList (x:xs) (y:ys) = [x, y] ++ (mixList xs ys)
mixList _ _ = []

-- function to change an item to the one specified as the parameter
-- written by: Junyang Xin
change x _ = x

-- modified depth-first search which outputs a list of edges visited during the depth-first search
-- written by: Junyang Xin
newDepthFirstSearch :: (Ix a, Num w) => a -> (Graph a w) -> [(a, a)]
newDepthFirstSearch start g = reverse (dfs [(start, start)] [])
  where 
    dfs [] vis = vis
    dfs ((parent, child):cs) vis 
	| elem child (map snd vis) = dfs cs vis
	| otherwise  = dfs ((zip (map (change child) (adjacent g child)) (adjacent g child)) ++ cs) ((parent, child):vis)

-- Dijkstra's shortes path algorithm
-- written by: Junyang Xin
data Cost w = Finite w | Infinity
			deriving (Eq, Ord, Show)			
			
-- function to add costs
-- written by: Junyang Xin
addCosts :: Num w => Cost w -> Cost w -> Cost w
addCosts (Finite w1) (Finite w2) = Finite (w1 + w2)
addCosts _ _ = Infinity

-- Function to look up the cost of a given edge
-- written by: Junyang Xin
lookUp :: (Ix n, Num w, Ord w) => n -> Graph n w -> n -> Cost w
lookUp x graph y
	| edgeIn graph (x, y) = Finite (weight x y graph)
	| x == y 			  = Finite 0
	| otherwise 	  	  = Infinity
	
-- function to remove an item from a list
-- written by: Junyang Xin
remove :: Eq a => a -> [a] -> [a]
remove _ [] = []
remove x (y:ys)
	| x == y 	= ys
	| otherwise = y : (remove x ys)
	
-- apply the Dijkstra's algorithm to a graph with the initial status specified
-- ps is the list of path costs of every vertex in a grahp. It represents the intitial status of applying the algorithm.
-- written by: Junyang Xin
allPaths :: (Ix n, Num w, Ord w) => n -> Graph n w -> [(Cost w, n)]
allPaths start graph 
	= pickVertex graph ps
		where ps = map (findPathCost start graph) (graphNodes graph) 

-- function to find the cost of path between two vertices
-- written by: Junyang Xin
findPathCost start graph end = ((lookUp start graph end), end)

-- function of Dijkstra's algorithm
-- it picks and removes a vertex with minimum path cost from the non-visited list and add it into the visited list
-- written by: Junyang Xin
pickVertex :: (Ix n, Num w, Ord w) => Graph n w -> [(Cost w, n)] -> [(Cost w, n)]
pickVertex graph [] = []
pickVertex graph (x:xs) = (minimum (x:xs)) : (pickVertex graph (map (relaxation graph (minimum (x:xs))) (remove (minimum (x:xs)) (x:xs))))

-- function to update the path costs of the non-visited vertices
-- written by: Junyang Xin
relaxation :: (Ix n, Num w, Ord w) => Graph n w -> (Cost w, n) -> (Cost w, n) -> (Cost w, n)
relaxation graph (cmin, j) (c, id)
	| newCost < c	= (newCost, id)
	| otherwise		= (c, id)
	where newCost = addCosts cmin (lookUp j graph id)

-- function to record the intermediate path costs of the non-visited vertices during the Dijkstra's algorithm running
-- these intermediate path costs are used to animate the updating of path costs of non-visited vertices	
-- written by: Junyang Xin
pickVertexWithItmCosts :: (Ix n, Num w, Ord w) => Graph n w -> [(Cost w, n)] -> [[(Cost w, n)]]
pickVertexWithItmCosts graph [] = []
pickVertexWithItmCosts graph (x:xs) 
	| fst (minimum (x:xs)) == Infinity = []
	| otherwise 						  = ((minimum (x:xs)) : (map (relaxation graph (minimum (x:xs))) (remove (minimum (x:xs)) (x:xs)))) : (pickVertexWithItmCosts graph (map (relaxation graph (minimum (x:xs))) (remove (minimum (x:xs)) (x:xs))))

-- apply the pickVertexWithItmCosts function to a graph	
-- written by: Junyang Xin
allPathsWithItmCosts :: (Ix n, Num w, Ord w) => n -> Graph n w -> [[(Cost w, n)]]
allPathsWithItmCosts start graph
	= pickVertexWithItmCosts graph ps
		where ps = map (findPathCost start graph) (graphNodes graph)

-- function to record the intermediate lists of non-visited vertices
-- these intermediate lists of vertices are used to help with updating the costs
-- written by: Junyang Xin		
pickVertexWithLeftVertices :: (Ix n, Num w, Ord w) => Graph n w -> [(Cost w, n)] -> [[n]]
pickVertexWithLeftVertices graph [] = []
pickVertexWithLeftVertices graph (x:xs)
	| fst (minimum (x:xs)) == Infinity = []
	| otherwise						   = (map snd (remove (minimum (x:xs)) (x:xs))) : (pickVertexWithLeftVertices graph (map (relaxation graph (minimum (x:xs))) (remove (minimum (x:xs)) (x:xs))))

-- apply the pickVertexWithLeftVertices function with the initial status provided	
-- written by: Junyang Xin
allPathsWithLeftVertices :: (Ix n, Num w, Ord w) => n -> Graph n w -> [[n]]		
allPathsWithLeftVertices start graph
	= pickVertexWithLeftVertices graph ps
		where ps = map (findPathCost start graph) (graphNodes graph)

-- function to convert the cost into string which can be used to draw	
-- written by: Junyang Xin
representCost :: (Num w, Ord w) => Cost w -> String
representCost (Finite w) = show w
representCost Infinity = "Inf"		

------------------------------------------- 
--Dijkstra's algorithm with path recorded--
-------------------------------------------

-- function to help to initialize the status of a graph's shortest path tree at the very begining of Dijkstra's algorithm
-- written by: Junyang Xin
lookUpWithPath x graph y array
	| edgeIn graph (x, y) = array // [(y, x)]
	| otherwise 	  	  = array
	
-- function to apply the lookUpWithPath function to a graph with a start vertex specified
-- written by: Junyang Xin
findPathCostWithPath :: (Ix n, Num w) => n -> Graph n w -> Array n n -> [n] -> Array n n
findPathCostWithPath start graph array [] 	  = array
findPathCostWithPath start graph array (x:xs) = findPathCostWithPath start graph (lookUpWithPath start graph x array) xs	

-- function to update the parent of a vertex during the search
-- written by: Junyang Xin
relaxationWithPath :: (Ix n, Num w, Ord w) => Graph n w -> Array n n -> (Cost w, n) -> (Cost w, n) -> Array n n
relaxationWithPath graph array (cmin, j) (c, id)
	| newCost < c	= array // [(id, j)]
	| otherwise		= array
	where newCost = addCosts cmin (lookUp j graph id)

-- apply the above function relaxationWithPath to a list of pairs in the format of (cost, vertexid)
-- written by: Junyang Xin
updatePath graph array (cmin, j) [] = array	
updatePath graph array (cmin, j) (x:xs) = updatePath graph (relaxationWithPath graph array (cmin, j) x) (cmin, j) xs

-- function to record the parents of each vertex in the shortest path tree
-- the output is an array with the index as the the child and the item of the corresponding index is the parent		
-- written by: Junyang Xin
pickVertexWithPath :: (Ix n, Num w, Ord w) => Graph n w -> Array n n -> [(Cost w, n)] -> Array n n
pickVertexWithPath graph array [] = array
pickVertexWithPath graph array (x:xs) = (pickVertexWithPath graph (updatePath graph array (minimum (x:xs)) (remove (minimum (x:xs)) (x:xs))) (map (relaxation graph (minimum (x:xs))) (remove (minimum (x:xs)) (x:xs))))

-- apply the Dijkstra's algorithm to a graph and produce an array with the index as the the child and the item of the corresponding index is the parent		
-- written by: Junyang Xin
allPathsWithPath :: (Ix n, Num n, Enum n, Num w, Ord w) => n -> Graph n w -> Array n n
allPathsWithPath start graph 
	= pickVertexWithPath graph initArray ps
		where 
			ps = map (findPathCost start graph) (graphNodes graph)
			initArray = (findPathCostWithPath start graph (array (1, (last (graphNodes graph))) [(i, -1) | i <- (graphNodes graph)]) (graphNodes graph))

-- function to find the path of Dijkstra's algorithm with start and target vertex specified
-- written by: Junyang Xin
findParents start target array 
	| array!target == -1 		= []
	| otherwise 				= (array!target) : (findParents start (array!target) array)
	
-- listOfPathVertices start target array = reverse (target : (findParents start target array))

-- listOfPathVerticesPairs start target array = zip (init pathlist) (tail pathlist)
	-- where 
		-- pathlist = listOfPathVertices start target array		

-- test on the shortest path algorithm		
test = allPathsWithPath 1 graph2

-- Animating the Dijkstra's algorithm
-- written by: Junyang Xin
makeSequence xs = (sequence_ xs)

-- functions to make edges with a start vertex specified and a list of target vertices
-- written by: Junyang Xin
makeEdges x [] = []
makeEdges x (y:ys) = (x, y) : (makeEdges x ys)

-- function to represent the edges with the coordinations of start vertex and target vertex
-- written by: Junyang Xin
setEdgeLocation cordArray edges = [(cordArray!start, cordArray!end) | (start, end) <- edges]

-- function to represent the edges with polyline which can be drawn
-- written by: Junyang Xin
makeEdgesToDraw edges = [polyline (map trans [start, end]) | (start, end) <- edges]

-- function to draw a list of edges on a window
-- written by: Junyang Xin
drawOutEdges window color edgesToDraw = [drawInWindow window (withColor color e) | e <- edgesToDraw]

-- function to represent the vertex with circle and also assign it its position on the plane
-- written by: Junyang Xin
makeVertexToDraw (x, y) = Translate (x, y) node

-- function to draw a vertex on a window
-- written by: Junyang Xin
drawOutVertex window color vertexToDraw = drawRegionInWindow window color vertexToDraw

-- function to represent the vertex id with text which can be drawn
-- written by: Junyang Xin
makeVertexIdToDraw vertexId (x, y) = text (trans (x-0.08, y+0.08)) (show vertexId)

-- function to draw the vertex id on a window
-- written by: Junyang Xin
drawOutVertexId window color vertexIdToDraw = drawInWindow window (withColor color vertexIdToDraw)

-- function to represent the cost with text which can be drawn
-- written by: Junyang Xin
makeCostToDraw cost (x, y) = text (trans (x - 0.08 , y - 0.08)) (representCost cost)

-- function to draw the path cost of a vertex
-- written by: Junyang Xin
drawOutCost window color costToDraw = drawInWindow window (withColor color costToDraw)

-- function to check if an edge is in the consideration
-- written by: Junyang Xin
isOptional [] _ = []
isOptional (c:cs) nonVisitedVertices
	| elem c nonVisitedVertices	= c : (isOptional cs nonVisitedVertices)
	| otherwise	= isOptional cs nonVisitedVertices
	
-- function to animate Dijkstra's shortest path algorithm
-- written by: Junyang Xin
animateDjkAlgorithm graph window [] _ _ _ = []
animateDjkAlgorithm graph window _ [] _ _ = []
animateDjkAlgorithm graph window _ _ [] _ = []
animateDjkAlgorithm graph window ((cost, vertex):xs) (costs:cs) (leftVertices:lvs) vertexCord 
	 = drawVertexAndId : (makeSequence (drawOptionalEdge ++ updateCost)) : animateDjkAlgorithm graph window xs cs lvs vertexCord								
		where
		drawVertexAndId = (makeSequence [(drawOutVertex window Green (makeVertexToDraw (vertexCord!vertex))), (drawOutVertexId window Black (makeVertexIdToDraw vertex (vertexCord!vertex)))])
		drawOptionalEdge = (drawOutEdges window Blue (makeEdgesToDraw	(setEdgeLocation vertexCord	(makeEdges vertex (isOptional (adjacent graph vertex) leftVertices)))))
		updateCost = [drawOutVertex window Red (makeVertexToDraw (vertexCord!vertex)) | vertex <- leftVertices] ++ [drawOutVertexId window Black (makeVertexIdToDraw vertex (vertexCord!vertex)) | vertex <- leftVertices] ++ [drawOutCost window Black (makeCostToDraw c (vertexCord!id))| (c, id) <- costs]

-- function to animate Dijkstra's shortest path algortihm with the shortest path tree being drawn
-- written by: Junyang Xin
newAnimateDjkAlgorithm graph window [] _ _ _ _ = []
newAnimateDjkAlgorithm graph window _ [] _ _ _ = []
newAnimateDjkAlgorithm graph window _ _ [] _ _ = []
newAnimateDjkAlgorithm graph window _ _ _ [] _ = []
newAnimateDjkAlgorithm graph window ((cost, vertex):xs) (costs:cs) (leftVertices:lvs) (path:paths) vertexCord
	 = (makeSequence (drawPathOfShortestPathTree ++ drawVertexAndId)) : (makeSequence (drawOptionalEdge ++ updateCost)) : newAnimateDjkAlgorithm graph window xs cs lvs paths vertexCord								
		where
			drawPathOfShortestPathTree = (drawOutEdges window Green (makeEdgesToDraw (setEdgeLocation vertexCord path))) ++ (drawOutEdges window Green (makeEdgesToDraw (setEdgeLocation vertexCord path)))
			drawVertexAndId = [(drawOutVertex window Green (makeVertexToDraw (vertexCord!vertex))), (drawOutVertexId window Black (makeVertexIdToDraw vertex (vertexCord!vertex))), (drawOutCost window Black (makeCostToDraw (fst (head costs)) (vertexCord!vertex)))]
			drawOptionalEdge = (drawOutEdges window Blue (makeEdgesToDraw (setEdgeLocation vertexCord (makeEdges vertex (isOptional (adjacent graph vertex) leftVertices))))) ++ (drawOutEdges window Blue (makeEdgesToDraw (setEdgeLocation vertexCord (makeEdges vertex (isOptional (adjacent graph vertex) leftVertices)))))
			updateCost = [drawOutVertex window Red (makeVertexToDraw (vertexCord!vertex)) | vertex <- leftVertices] ++ [drawOutVertexId window Black (makeVertexIdToDraw vertex (vertexCord!vertex)) | vertex <- leftVertices] ++ [drawOutCost window Black (makeCostToDraw c (vertexCord!id))| (c, id) <- costs]

-- function to store the items of an array into a list	 
-- written by: Junyang Xin
turnArrayToList :: Ix n => [n] -> Array n n -> [(n, n)]
turnArrayToList [] _ = []
turnArrayToList (x:xs) array = (x, array!x) : (turnArrayToList xs array)

-- function to create the shortest path tree
-- written by: Junyang Xin
shortestPathTree graph [] = []
shortestPathTree graph ((child, parent):xs) 
	| parent == (-1)	= [] : shortestPathTree graph xs
	| otherwise			= [(parent, child)] : shortestPathTree graph xs

-- animate Dijkstra's Shortest Paths algorithm
-- written by: Junyang Xin	
mainDijkShortestPath = runGraphics $
	do src <- readFile "DijkstraSTP.txt"
	   let edges = map (split.words) (tail (lines src))
	       maxBound = read (head (lines src))
	   -- Start point
	       origin = 1
	   -- Directed graph
	       graph = mkGraph True (1, maxBound) edges
	   -- ids of vertices 
	       vertexIds = graphNodes graph
	   -- list of vertex ids and the corresponding positions
	       positionsAndIds = zip locations vertexIds
	   -- create an array of coordinations of the vertices for convinient use
	       vertexCord = array (1, maxBound) [(index, (x, y)) | ((x, y), index) <- positionsAndIds]
	   -- edges represented by two coordinations of start vertex and target vertex
	       edgesOfVertices = [(vertexCord!start, vertexCord!end) | (start, end, weight) <- edges]
	   -- vertices to draw
	       vertexToDraw = [Translate (x, y) node | (x, y) <- (take maxBound locations)]
	   -- edges represented by polyline to draw
	       edgesToDraw = [polyline (map trans [start, end]) | (start, end) <- edgesOfVertices]
	   -- vertex ids to draw
	       vertexIdsToDraw = [text (trans (x-0.08, y+0.08)) (show z) | ((x, y), z) <- positionsAndIds]
	   -- positions of weights to draw
	       positionOfWeights = [((calculateMidCord (vertexCord!start) (vertexCord!end)), weight) | (start, end, weight) <- edges]
	   -- weights to draw
	       weightsToDraw = [text (trans (x, y)) (show z) | ((x, y), z) <- positionOfWeights] 
	   w <- openWindow "Dijkstra's Shortest Paths" (800, 650)
	   drawInWindow w (withColor White (polygon [(0,0), (799,0), (799,649), (0,649)]))
	   -- actions to animate the Dijkstra's algorithm
	   let 
		   animateAlgorithmDraw = newAnimateDjkAlgorithm graph w (allPaths origin graph) (allPathsWithItmCosts origin graph) (allPathsWithLeftVertices origin graph) (shortestPathTree graph (turnArrayToList (map snd (allPaths origin graph)) (allPathsWithPath origin graph))) vertexCord
		   userInteraction = map (change (getKey w)) animateAlgorithmDraw
		   userInteractionList = [(sequence_ [action]) | action <- userInteraction]
	   let 
		   arrowPositions = map calPosition edgesOfVertices
		   arrowsToDraw = [polygon (map trans position) | position <- arrowPositions]		   
	   let drawWithInteraction = mixList userInteractionList animateAlgorithmDraw
	   -- draw out the vertices
	   sequence_ [drawRegionInWindow w Red n | n <- vertexToDraw]
	   -- draw out the edges
	   sequence_ [drawInWindow w (withColor Yellow e) | e <- edgesToDraw]
	   -- draw out the arrows of edges
	   sequence_ [drawInWindow w (withColor Black arrow) | arrow <- arrowsToDraw]
	   -- draw out the vertex ids
	   sequence_ [drawInWindow w (withColor Black t) | t <- vertexIdsToDraw]
	   -- draw out the weights
	   sequence_ [drawInWindow w (withColor Black t) | t <- weightsToDraw]
	   sequence_ drawWithInteraction
	   spaceClose w
	   where
			split [start, end, weight] = ((read start), (read end), (read weight))

-- function to calculate the coordinate of the middle point between two vertices on the plane
-- written by: Junyang Xin
calculateMidCord :: Myvertex -> Myvertex -> Myvertex
calculateMidCord (x1, y1) (x2, y2) = (((x1 + x2) / 2), ((y1 + y2) / 2))

-------------------------------------
-- functions for Kruskal algorithm --
-------------------------------------

-- function of picking the edge with the minimum cost
-- written by: Junyang Xin
pickMinEdge :: (Ix n, Num w, Ord w) => [(n, n, w)] -> (n, n, w)
pickMinEdge [x] = x
pickMinEdge ((s1, t1, w1) : (s2, t2, w2) : edges)
	| w1 > w2	= pickMinEdge ((s2, t2, w2) : edges)
	| otherwise = pickMinEdge ((s1, t1, w1) : edges)

-- function to check if two vertices are in a connected set
-- written by: Junyang Xin
checkConnectivity :: Ix n => (n, n) -> [[n]] -> Bool
checkConnectivity _ [] = False
checkConnectivity (s, t) (x:xs)
	| (elem s x) && (elem t x)	= True
	| otherwise					= checkConnectivity (s, t) xs

-- function to find the connected set containing a certain vertex
-- written by: Junyang Xin
findConnSet :: Ix n => n -> [[n]] -> [n]
findConnset _ [] = []
findConnSet v (x:xs)
	| elem v x	= x
	| otherwise = findConnSet v xs
	
-- function to update the connected sets
-- written by: Junyang Xin
updateConnSets :: Ix n => (n, n) -> [[n]] -> [[n]]
updateConnSets _ [] = []
updateConnSets (s, t) xs
	= ((findConnSet s xs) ++ (findConnSet t xs)) : (remove (findConnSet t xs) (remove (findConnSet s xs) xs))
	
-- functions to get the first element from a tuple
-- written by: Junyang Xin
tupleFst (x, y, z) = x

-- function to get the second element from a tuple
-- written by: Junyang Xin
tupleSnd (x, y, z) = y
 	
-- function of Kruskal algorithm
-- written by: Junyang Xin
kruskal :: (Ix n, Num w, Ord w) => [(n, n, w)] -> [[n]] -> [(n, n)] -> [(n, n)]
kruskal [] _ mst = reverse mst
kruskal edges sets mst
	| (checkConnectivity minEdge sets) == True			= kruskal (remove (pickMinEdge edges) edges) sets mst
	| otherwise											= kruskal (remove (pickMinEdge edges) edges) (updateConnSets minEdge sets) (minEdge : mst) 
	where 
		minEdge = (tupleFst (pickMinEdge edges), tupleSnd (pickMinEdge edges))
		
-- function of animating the Kruskal algorithm
-- written by: Junyang Xin
animateKruskal window [] _	 = []		
animateKruskal window (e:es) vertexCord = drawMSTEdge : animateKruskal window es vertexCord
								where
									drawMSTEdge = (makeSequence (recolorVertices ++ drawEdge))
									recolorVertices = [(drawOutVertex window Green (makeVertexToDraw (vertexCord!(fst e)))), (drawOutVertexId window Black (makeVertexIdToDraw (fst e) (vertexCord!(fst e)))), (drawOutVertex window Green (makeVertexToDraw (vertexCord!(snd e)))), (drawOutVertexId window Black (makeVertexIdToDraw (snd e) (vertexCord!(snd e))))]
									drawEdge = (drawOutEdges window Green (makeEdgesToDraw (setEdgeLocation vertexCord [e]))) ++ (drawOutEdges window Green (makeEdgesToDraw (setEdgeLocation vertexCord [e])))

-- animate Kruskal's MST algorithm
-- written by: Junyang Xin
mainKruskal = runGraphics $
	do src <- readFile "KruskalMST.txt"
	   let edges = map (split.words) (tail (lines src))
	       maxBound = read (head (lines src))
	   -- Start point
	       origin = 1
	   -- Directed graph
	       graph = mkGraph False (1, maxBound) edges
	   -- ids of vertices 
	       vertexIds = graphNodes graph
	   -- list of vertex ids and the corresponding positions
	       positionsAndIds = zip locations vertexIds
	   -- create an array of coordinations of the vertices for convinient use
	       vertexCord = array (1, maxBound) [(index, (x, y)) | ((x, y), index) <- positionsAndIds]
	   -- edges represented by two coordinations of start vertex and target vertex
	       edgesOfVertices = [(vertexCord!start, vertexCord!end) | (start, end, weight) <- edges]
	   -- vertices to draw
	       vertexToDraw = [Translate (x, y) node | (x, y) <- (take maxBound locations)]
	   -- edges represented by polyline to draw
	       edgesToDraw = [polyline (map trans [start, end]) | (start, end) <- edgesOfVertices]
	   -- vertex ids to draw
	       vertexIdsToDraw = [text (trans (x-0.08, y+0.08)) (show z) | ((x, y), z) <- positionsAndIds]
	   -- positions of weights to draw
	       positionOfWeights = [((calculateMidCord (vertexCord!start) (vertexCord!end)), weight) | (start, end, weight) <- edges]
	   -- weights to draw
	       weightsToDraw = [text (trans (x, y)) (show z) | ((x, y), z) <- positionOfWeights] 
	   w <- openWindow "Kruskal's MST" (800, 650)
	   drawInWindow w (withColor White (polygon [(0,0), (799,0), (799,649), (0,649)]))
	   -- actions to animate the Kruskal's algorithm
	   let 
		   mst = kruskal (edgesD graph) [[v] | v <- (graphNodes graph)] []
		   animateAlgorithmDraw = animateKruskal w mst vertexCord
		   userInteraction = map (change (getKey w)) animateAlgorithmDraw
		   userInteractionList = [(sequence_ [action]) | action <- userInteraction]
	   -- let 
		   -- arrowPositions = map calPosition edgesOfVertices
		   -- arrowsToDraw = [polygon (map trans position) | position <- arrowPositions]		   
	   let drawWithInteraction = mixList userInteractionList animateAlgorithmDraw
	   -- draw out the vertices
	   sequence_ [drawRegionInWindow w Red n | n <- vertexToDraw]
	   -- draw out the edges
	   sequence_ [drawInWindow w (withColor Yellow e) | e <- edgesToDraw]
	   -- draw out the vertex ids
	   sequence_ [drawInWindow w (withColor Black t) | t <- vertexIdsToDraw]
	   -- draw out the weights
	   sequence_ [drawInWindow w (withColor Black t) | t <- weightsToDraw]
	   -- arrows to draw	   
	   --sequence_ [drawInWindow w (withColor Black arrow) | arrow <- arrowsToDraw]
	   sequence_ drawWithInteraction
	   spaceClose w
	   where
			split [start, end, weight] = ((read start), (read end), (read weight))
	
-- function to calculate the positions of the triangle representing the direction of an edge
-- written by: Junyang Xin
calPosition :: (Myvertex, Myvertex) -> [Myvertex]
calPosition ((x1, y1), (x2, y2))
	| x1 == x2 && y1 > y2	= [midPoint, ((fst midPoint) - 0.08, (snd midPoint) + 0.08), ((fst midPoint) + 0.08, (snd midPoint) + 0.08)]
	| x1 == x2 && y1 < y2	= [midPoint, ((fst midPoint) - 0.08, (snd midPoint) - 0.08), ((fst midPoint) + 0.08, (snd midPoint) - 0.08)]
	| y1 == y2 && x1 > x2	= [midPoint, ((fst midPoint) + 0.08, (snd midPoint) + 0.08), ((fst midPoint) + 0.08, (snd midPoint) - 0.08)]
	| y1 == y2 && x1 < x2	= [midPoint, ((fst midPoint) - 0.08, (snd midPoint) + 0.08), ((fst midPoint) - 0.08, (snd midPoint) - 0.08)]
	| otherwise				= [midPoint, ((fst midPoint), (getTriangleVertex (snd midPoint) y1)), ((getTriangleVertex (fst midPoint) x1), (snd midPoint))]
	where
		midPoint = calculateMidCord (x1, y1) (x2, y2)

-- function to calculate the coordinates of two vertices of the triangle representing the arrow on an edge
-- written by: Junyang Xin
getTriangleVertex x1 x2
	| x1 > x2	= x1 - 0.08
	| otherwise = x1 + 0.08