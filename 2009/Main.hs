import Data.List
import Data.Maybe
import Data.Tuple

type Index = Int

data BExp = Prim Bool | IdRef Index | Not BExp | And BExp BExp | Or BExp BExp
            deriving (Eq, Ord, Show)

type Env = [(Index, Bool)]

type NodeId = Int

type BDDNode =  (NodeId, (Index, NodeId, NodeId))

type BDD = (NodeId, [BDDNode])

------------------------------------------------------
-- PART I

-- Pre: The item is in the given table
lookUp :: Eq a => a -> [(a, b)] -> b
lookUp 
  = (fromJust .) . lookup

checkSat :: BDD -> Env -> Bool
checkSat (root, nodes) env
  | goRight && rightBottom = right == 1
  | goRight                = checkSat (right, nodes) env
  | leftBottom             = left == 1
  | otherwise              = checkSat (left, nodes) env
  where
    (id, left, right) = lookUp root nodes
    goRight = lookUp id env
    leftBottom = left `elem` [0, 1]
    rightBottom = right `elem` [0, 1]

sat :: BDD -> [[(Index, Bool)]]
sat (0, _)
  = []
sat (1, _)
  = [[]]
sat (root, nodes)
  = map ((id, False) :) leftSat ++ map ((id, True) :) rightSat 
  where
    (id, left, right) = lookUp root nodes
    leftSat = sat (left, nodes)
    rightSat = sat (right, nodes)

------------------------------------------------------
-- PART II

simplify :: BExp -> BExp
simplify (Not (Prim False))
  = Prim True
simplify (Not (Prim True))
  = Prim False
simplify (And (Prim True) (Prim True))
  = Prim True
simplify (And (Prim _) (Prim _))
  = Prim False
simplify (Or (Prim False) (Prim False))
  = Prim False
simplify (Or (Prim _) (Prim _))
  = Prim True
simplify expr
  = expr

restrict :: BExp -> Index -> Bool -> BExp
restrict (IdRef id') id val
  | id' == id = Prim val
  | otherwise = IdRef id' 
restrict (Not expr) id val
  = simplify (Not (restrict expr id val))
restrict (And left right) id val
  = simplify (And (restrict left id val) (restrict right id val))
restrict (Or left right) id val
  = simplify (Or (restrict left id val) (restrict right id val))
restrict expr _ _
  = expr

------------------------------------------------------
-- PART III

-- Pre: Each variable index in the BExp appears exactly once
--     in the Index list; there are no other elements
-- The question suggests the following definition (in terms of buildBDD')
-- but you are free to implement the function differently if you wish.
buildBDD :: BExp -> [Index] -> BDD
buildBDD
  = flip buildBDD' 2

-- Potential helper function for buildBDD which you are free
-- to define/modify/ignore/delete/embed as you see fit.
buildBDD' :: BExp -> NodeId -> [Index] -> BDD
buildBDD' (Prim True) _ []
  = (1, [])
buildBDD' (Prim False) _ []
  = (0, [])
buildBDD' expr nodeId (id : ids) 
  = (nodeId, (nodeId, (id, leftId, rightId)) : left ++ right) 
  where
    (leftId, left) = buildBDD' (restrict expr id False) (2 * nodeId) ids
    (rightId, right) = buildBDD' (restrict expr id True) (2 * nodeId + 1) ids

------------------------------------------------------
-- PART IV

-- Pre: Each variable index in the BExp appears exactly once
--      in the Index list; there are no other elements
deepLookUp :: Eq a => a -> [(a, a)] -> a
deepLookUp key table
  | key == value = value
  | otherwise    = deepLookUp value table
  where
    value = lookUp key table

buildROBDD :: BExp -> [Index] -> BDD
buildROBDD expr ids
  = eliminateNodes (shareSubtrees nodes)
  where
    (root, nodes) = buildBDD expr ids

    eliminateNodes :: [BDDNode] -> BDD
    eliminateNodes nodes
      = (root', 
          [(n, (v, deepLookUp l replacements', deepLookUp r replacements')) 
          | (n, (v, l, r)) <- nodes
          , (n, n) `elem` nonReplaced]
        )
      where
        eliminatedNodes = filter (\(_, (_, l, r)) -> l == r) nodes
        replacements = map (\(n, (_, n', _)) -> (n, n')) eliminatedNodes
        nonReplaced = (0, 0) : (1, 1) : 
                      [(n, n) | (n, _) <- nodes
                              , n `notElem` map fst replacements]
        replacements' = replacements ++ nonReplaced
        root' = deepLookUp root replacements'
    
    shareSubtrees :: [BDDNode] -> [BDDNode]
    shareSubtrees nodes
      | nodes == nodes' = nodes'
      | otherwise       = shareSubtrees nodes'
      where
        redundancies = (groupBy (\(_, a) (_, b) -> a == b) . sortOn snd) nodes
        representatives = map (fst . head) redundancies
        replace a = map (\(n, _) -> (n, a))
        replacements = (0, 0) : (1, 1) : 
                       concat (zipWith replace representatives redundancies)
        nodes' = [(n, (v, lookUp l replacements, lookUp r replacements))
                  | (n, (v, l, r)) <- nodes
                  , n `elem` representatives]

------------------------------------------------------
-- Examples for testing...

b1, b2, b3, b4, b5, b6, b7, b8 :: BExp
b1 = Prim False
b2 = Not (And (IdRef 1) (Or (Prim False) (IdRef 2)))
b3 = And (IdRef 1) (Prim True)
b4 = And (IdRef 7) (Or (IdRef 2) (Not (IdRef 3)))
b5 = Not (And (IdRef 7) (Or (IdRef 2) (Not (IdRef 3))))
b6 = Or (And (IdRef 1) (IdRef 2)) (And (IdRef 3) (IdRef 4))
b7 = Or (Not (IdRef 3)) (Or (IdRef 2) (Not (IdRef 9)))
b8 = Or (IdRef 1) (Not (IdRef 1))

bdd1, bdd2, bdd3, bdd4, bdd5, bdd6, bdd7, bdd8 :: BDD
bdd1 = (0,[])
bdd2 = (2,[(4,(2,1,1)),(5,(2,1,0)),(2,(1,4,5))])
bdd3 = (5,[(5,(1,0,1))])
bdd4 = (2,[(2,(2,4,5)),(4,(3,8,9)),(8,(7,0,1)),(9,(7,0,0)),
           (5,(3,10,11)),(10,(7,0,1)),(11,(7,0,1))])
bdd5 = (3,[(4,(3,8,9)),(3,(2,4,5)),(8,(7,1,0)),(9,(7,1,1)),
           (5,(3,10,11)),(10,(7,1,0)),(11,(7,1,0))])
bdd6 = (2,[(2,(1,4,5)),(4,(2,8,9)),(8,(3,16,17)),(16,(4,0,0)),
           (17,(4,0,1)),(9,(3,18,19)),(18,(4,0,0)),(19,(4,0,1)),
           (5,(2,10,11)),(10,(3,20,21)),(20,(4,0,0)),(21,(4,0,1)),
           (11,(3,22,23)),(22,(4,1,1)),(23,(4,1,1))])
bdd7 = (6,[(6,(2,4,5)),(4,(3,8,9)),(8,(9,1,1)),(9,(9,1,0)),
           (5,(3,10,11)),(10,(9,1,1)),(11,(9,1,1))])
bdd8 = (2,[(2,(1,1,1))])

