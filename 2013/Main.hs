type BinHeap a = [BinTree a]

data BinTree a = Node a Int (BinHeap a)
               deriving (Eq, Ord, Show)

--------------------------------------------------------------
-- PART I

value :: BinTree a -> a
value (Node v _ _)
  = v

rank :: BinTree a -> Int
rank (Node _ r _)
  = r

children :: BinTree a -> [BinTree a]
children (Node _ _ h)
  = h

combineTrees :: Ord a => BinTree a -> BinTree a -> BinTree a
combineTrees n@(Node v r h) n'@(Node v' r' h')
  | v < v'    = Node v (r + 1) (n' : h)
  | otherwise = Node v' (r + 1) (n : h')

--------------------------------------------------------------
-- PART II

extractMin :: Ord a => BinHeap a -> a
extractMin 
  = minimum . map value 

mergeHeaps :: Ord a => BinHeap a -> BinHeap a -> BinHeap a
mergeHeaps h@(t : ts) h'@(t' : ts')
  | rank t < rank t' = t : mergeHeaps ts h'
  | rank t > rank t' = t' : mergeHeaps ts' h
  | otherwise        = mergeHeaps [combineTrees t t'] (mergeHeaps ts ts')
mergeHeaps h []
  = h
mergeHeaps [] h'
  = h'

insert :: Ord a => a -> BinHeap a -> BinHeap a
insert v
  = mergeHeaps [Node v 0 []]

deleteMin :: Ord a => BinHeap a -> BinHeap a
deleteMin h
  = mergeHeaps [t | t <- h, t /= minTree] (reverse (children minTree))
  where
    minTree = snd (minimum (zip (map value h) h))

binSort :: Ord a => [a] -> [a]
binSort xs
  = map extractMin (take (length xs) (iterate deleteMin h))
  where
    h = foldr insert [] xs

--------------------------------------------------------------
-- PART III

toBinary :: BinHeap a -> [Int]
toBinary h
  = reverse (toBinary' h 0)
  where
    toBinary' :: BinHeap a -> Int -> [Int]
    toBinary' [] _
      = []
    toBinary' (t : ts) i
      | rank t == i = 1 : toBinary' ts (i + 1)
      | otherwise   = 0 : toBinary' (t : ts) (i + 1)

binarySum :: [Int] -> [Int] -> [Int]
binarySum b b'
  | carry == 0 = digits
  | otherwise  = 1 : digits
  where
    bLen = length b
    b'Len = length b'
    maxLen = max bLen b'Len
    padB = replicate (maxLen - bLen) 0 ++ b
    padB' = replicate (maxLen - b'Len) 0 ++ b'
    (digits, carry) = binarySum' padB padB'

    binarySum' :: [Int] -> [Int] -> ([Int], Int)
    binarySum' (d : ds) (d' : ds')
      | dSum < 2  = (d + d' + c : rest, 0)
      | dSum == 2 = (0 : rest, 1)
      | otherwise = (1 : rest, 1)
      where
        dSum = d + d' + c
        (rest, c) = binarySum' ds ds'
    binarySum' ds []
      = (ds, 0)
    binarySum' [] ds'
      = (ds', 0)

------------------------------------------------------
-- Some sample trees...

t1, t2, t3, t4, t5, t6, t7, t8 :: BinTree Int
-- Note: t7 is the result of merging t5 and t6

-- t1 to t4 appear in Figure 1...
t1 = Node 4 0 []
t2 = Node 1 1 [Node 5 0 []]
t3 = Node 2 2 [Node 8 1 [Node 9 0 []], 
               Node 7 0 []]
t4 = Node 2 3 [Node 3 2 [Node 6 1 [Node 8 0 []], 
                         Node 10 0 []],
               Node 8 1 [Node 9 0 []],
               Node 7 0 []]

-- t5 and t6 are on the left of Figure 2; t7 is on the
-- right
t5 = Node 4 2 [Node 6 1 [Node 8 0 []], 
                         Node 10 0 []]
t6 = Node 2 2 [Node 8 1 [Node 9 0 []], Node 7 0 []]
t7 = Node 2 3 [Node 4 2 [Node 6 1 [Node 8 0 []], Node 10 0 []],
               Node 8 1 [Node 9 0 []], 
               Node 7 0 []]

-- An additional tree...
t8 = Node 12 1 [Node 16 0 []]

------------------------------------------------------
-- Some sample heaps...

h1, h2, h3, h4, h5, h6, h7 :: BinHeap Int
-- Two arbitrary heaps for testing...
h1 = [t2, t7]
h2 = [Node 1 2 [Node 12 1 [Node 16 0 []],
                Node 5 0 []],
      Node 2 3 [Node 4 2 [Node 6 1 [Node 8 0 []],
                          Node 10 0 []],
                Node 8 1 [Node 9 0 []],
                Node 7 0 []]]

-- h3 is shown in Figure 3...
h3 = [t1, t2, t4]

-- Two additional heaps, used below. They are shown
-- in Figure 4(a)...

h4 = [t2, t5]
h5 = [t1, t8]

-- h6 is the result of merging h4 and h5, shown in Figure 4(b)...
h6 = [Node 4 0 [],
      Node 1 3 [Node 4 2 [Node 6 1 [Node 8 0 []],
                          Node 10 0 []],
                Node 12 1 [Node 16 0 []],
                Node 5 0 []]]

-- h7 is shown in Figure 5...
h7 = [Node 4 3 [Node 4 2 [Node 12 1 [Node 16 0 []],
                          Node 5 0 []],
                Node 6 1 [Node 8 0 []],
                Node 10 0 []]]


