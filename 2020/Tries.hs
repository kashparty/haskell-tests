module Tries where

import Data.List hiding (insert)
import Data.Bits

import Types
import HashFunctions
import Examples

--------------------------------------------------------------------
-- Part I

-- Use this if you're counting the number of 1s in every
-- four-bit block...
bitTable :: [Int]
bitTable
  = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

countOnes :: Int -> Int
countOnes 0
  = 0
countOnes n
  = bitTable !! batch + countOnes (n `div` 16)
  where
    batch = n `mod` 16

countOnesFrom :: Int -> Int -> Int
countOnesFrom i n
  = popCount (n .&. (bit i - 1))

getIndex :: Int -> Int -> Int -> Int
getIndex n 0 b
  = n `mod` bit b
getIndex n i b
  = getIndex (n `div` bit b) (i - 1) b

-- Pre: the index is less than the length of the list
replace :: Int -> [a] -> a -> [a]
replace i xs x
  = before ++ x : after
  where
    (before, _ : after) = splitAt i xs

-- Pre: the index is less than or equal to the length of the list
insertAt :: Int -> a -> [a] -> [a]
insertAt i x xs
  = before ++ x : after
  where
    (before, after) = splitAt i xs 

--------------------------------------------------------------------
-- Part II

sumSubNode :: (Int -> Int) -> ([Int] -> Int) -> SubNode -> Int
sumSubNode f _ (Term n)
  = f n
sumSubNode f f' (SubTrie t)
  = sumTrie f f' t

sumTrie :: (Int -> Int) -> ([Int] -> Int) -> Trie -> Int
sumTrie _ f' (Leaf ns)
  = f' ns
sumTrie f f' (Node _ subs)
  = sum (map (sumSubNode f f') subs)

--
-- If you get the sumTrie function above working you can uncomment
-- these three functions; they may be useful in testing.
--
trieSize :: Trie -> Int
trieSize t
  = sumTrie (const 1) length t

binCount :: Trie -> Int
binCount t
  = sumTrie (const 1) (const 1) t

meanBinSize :: Trie -> Double
meanBinSize t
  = fromIntegral (trieSize t) / fromIntegral (binCount t)

member :: Int -> Hash -> Trie -> Int -> Bool
member v h (Leaf vs) b
  = v `elem` vs
member v h (Node bv subs) b
  | not (testBit bv i) = False
  | Term v' <- sub     = v == v' 
  | SubTrie t' <- sub  = member v (h `div` bit b) t' b
  where
    i = getIndex h 0 b
    n = countOnesFrom i bv
    sub = subs !! n

--------------------------------------------------------------------
-- Part III

insert :: HashFun -> Int -> Int -> Int -> Trie -> Trie
insert f d b v node
  = insert' f d b v 0 node 
  where
    insert' :: HashFun -> Int -> Int -> Int -> Int -> Trie -> Trie
    insert' f d b v _ (Leaf vs)
      | v `elem` vs = Leaf vs
      | otherwise   = Leaf (v : vs)
    insert' f 0 b v _ _
      = Leaf [v]
    insert' f d b v l node@(Node bv subs)
      | not (testBit bv i) = Node (setBit bv i) (insertAt n (Term v) subs) 
      | SubTrie t <- sub   = Node bv (replace n subs (SubTrie (insert' f (d - 1) b v (l + 1) t)))
      | otherwise          = if v == v' then node else Node bv (replace n subs sub')
      where
        i = getIndex (f v) l b
        n = countOnesFrom i bv
        sub = subs !! n
        Term v' = sub
        sub' = SubTrie (insert' f (d - 2) b v (l + 1) (insert' f (d - 1) b v' (l + 1) empty))

buildTrie :: HashFun -> Int -> Int -> [Int] -> Trie
buildTrie f d b
  = foldr (insert f d b) empty