import Data.List (maximumBy)
data SuffixTree = Leaf Int | Node [(String, SuffixTree)]
                deriving (Eq, Show)

------------------------------------------------------

isPrefix :: String -> String -> Bool
isPrefix [] _
  = True
isPrefix _ []
  = False
isPrefix (x : xs) (y : ys)
  = x == y && isPrefix xs ys

removePrefix :: String -> String -> String
removePrefix xs ys
--Pre: s is a prefix of s'
  = drop (length ys) xs

suffixes :: [a] -> [[a]]
suffixes xs
  = take (length xs) (iterate tail xs)

isSubstring :: String -> String -> Bool
isSubstring xs ys
  = any (isPrefix xs) (suffixes ys)

findSubstrings :: String -> String -> [Int]
findSubstrings xs ys
  = map snd $ filter (\(y, _) -> isPrefix xs y) (zip (suffixes ys) [0..])

------------------------------------------------------

getIndices :: SuffixTree -> [Int]
getIndices (Leaf i)
  = [i]
getIndices (Node bs)
  = concatMap (getIndices . snd) bs

partition :: Eq a => [a] -> [a] -> ([a], [a], [a])
partition (x : xs) (y : ys)
  | x == y    = (x : common, xRem, yRem)
  | otherwise = ([], x : xs, y : ys)
  where
    (common, xRem, yRem) = partition xs ys
partition xs ys
  = ([], xs, ys)

findSubstrings' :: String -> SuffixTree -> [Int]
findSubstrings' _ (Leaf i)
  = [i]
findSubstrings' s (Node [])
  = []
findSubstrings' s (Node ((a, st) : as))
  | null sRem = getIndices st
  | null aRem = findSubstrings' sRem st
  | otherwise = findSubstrings' s (Node as)
  where
    (common, sRem, aRem) = partition s a

------------------------------------------------------

insert :: (String, Int) -> SuffixTree -> SuffixTree
insert (s, n) (Node [])
  = Node [(s, Leaf n)]
insert (s, n) (Node ((a, t) : ts))
  | null p    = Node ((a, t) : ts')
  | null aRem = Node ((a, insert (sRem, n) t) : ts)
  | otherwise = Node ((p, Node [(sRem, Leaf n), (aRem, t)]) : ts)
  where
    (p, sRem, aRem) = partition s a
    Node ts' = insert (s, n) (Node ts)

-- This function is given
buildTree :: String -> SuffixTree
buildTree s
  = foldl (flip insert) (Node []) (zip (suffixes s) [0..])

------------------------------------------------------
-- Part IV

repeatedSubstrings :: String -> String -> SuffixTree -> [String]
repeatedSubstrings s s' (Leaf _)
  = [s]
repeatedSubstrings s s' (Node ts)
  = concatMap (\(a, t) -> repeatedSubstrings s' (s' ++ a) t) ts

longestRepeatedSubstring :: SuffixTree -> String
longestRepeatedSubstring st
  = (snd . maximum . zip (map length repeats)) repeats
  where
    repeats = repeatedSubstrings "" "" st

------------------------------------------------------
-- Example strings and suffix trees...

s1 :: String
s1
  = "banana"

s2 :: String
s2
  = "mississippi"

t1 :: SuffixTree
t1
  = Node [("banana", Leaf 0),
          ("a", Node [("na", Node [("na", Leaf 1),
                                   ("", Leaf 3)]),
                     ("", Leaf 5)]),
          ("na", Node [("na", Leaf 2),
                       ("", Leaf 4)])]

t2 :: SuffixTree
t2
  = Node [("mississippi", Leaf 0),
          ("i", Node [("ssi", Node [("ssippi", Leaf 1),
                                    ("ppi", Leaf 4)]),
                      ("ppi", Leaf 7),
                      ("", Leaf 10)]),
          ("s", Node [("si", Node [("ssippi", Leaf 2),
                                   ("ppi", Leaf 5)]),
                      ("i", Node [("ssippi", Leaf 3),
                                  ("ppi", Leaf 6)])]),
          ("p", Node [("pi", Leaf 8),
                      ("i", Leaf 9)])]

