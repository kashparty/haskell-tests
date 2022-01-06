import Data.Maybe
import Data.List
import Debug.Trace

type AttName = String

type AttValue = String

type Attribute = (AttName, [AttValue])

type Header = [Attribute]

type Row = [AttValue]

type DataSet = (Header, [Row])

data DecisionTree = Null |
                    Leaf AttValue |
                    Node AttName [(AttValue, DecisionTree)]
                  deriving (Eq, Show, Ord)

type Partition = [(AttValue, DataSet)]

type AttSelector = DataSet -> Attribute -> Attribute

xlogx :: Double -> Double
xlogx p
  | p <= 1e-100 = 0.0
  | otherwise   = p * log2 p
  where
    log2 x = log x / log 2

lookUp :: (Eq a, Show a, Show b) => a -> [(a, b)] -> b
lookUp x table
  = fromMaybe (error ("lookUp error - no binding for " ++ show x ++
                      " in table: " ++ show table))
              (lookup x table)

--------------------------------------------------------------------
-- PART I
--------------------------------------------------------------------

allSame :: Eq a => [a] -> Bool
allSame xs
  = and (zipWith (==) xs (tail xs))

remove :: Eq a => a -> [(a, b)] -> [(a, b)]
remove key table
  = [(k, v) | (k, v) <- table, k /= key]

lookUpAtt :: AttName -> Header -> Row -> AttValue
--Pre: The attribute name is present in the given header.
lookUpAtt name header row
  = fromJust $ find (`elem` values) row
  where
    values = lookUp name header

removeAtt :: AttName -> Header -> Row -> Row
removeAtt name header row
  = [att | att <- row, att `notElem` values]
  where
    values = lookUp name header

addToMapping :: Eq a => (a, b) -> [(a, [b])] -> [(a, [b])]
addToMapping (x, v) mapping
  | null xs   = (x, [v]) : ys
  | otherwise = (x, v : vs) : ys
  where
    (xs, ys) = partition ((x ==) . fst) mapping
    ((_, vs) : _) = xs

buildFrequencyTable :: Attribute -> DataSet -> [(AttValue, Int)]
--Pre: Each row of the data set contains an instance of the attribute
buildFrequencyTable (name, values) (header, rows)
  = zip values (map (fromMaybe 0 . (`lookup` table)) values)
  where
    groups = (group . sort . map (lookUpAtt name header)) rows
    table = zip (map head groups) (map length groups)

--------------------------------------------------------------------
-- PART II
--------------------------------------------------------------------

nodes :: DecisionTree -> Int
nodes Null
  = 0
nodes (Leaf _)
  = 1
nodes (Node _ children)
  = 1 + sum (map (nodes . snd) children)

evalTree :: DecisionTree -> Header -> Row -> AttValue
evalTree Null _ _
  = ""
evalTree (Leaf v) _ _
  = v
evalTree (Node name children) header row
  = evalTree (lookUp (lookUpAtt name header row) children) header row

--------------------------------------------------------------------
-- PART III
--------------------------------------------------------------------

--
-- Given...
-- In this simple case, the attribute selected is the first input attribute 
-- in the header. Note that the classifier attribute may appear in any column,
-- so we must exclude it as a candidate.
--
nextAtt :: AttSelector
--Pre: The header contains at least one input attribute
nextAtt (header, _) (classifierName, _)
  = head (filter ((/= classifierName) . fst) header)

partitionData :: DataSet -> Attribute -> Partition
partitionData (header, rows) (name, values)
  = map (\(value, rows) -> (value, (header', rows))) mapping
  where
    atts = map (lookUpAtt name header) rows
    withoutAtt = map (removeAtt name header) rows
    rowsByAtts = zip atts withoutAtt
    initMapping = zip values (repeat [])
    mapping = foldr addToMapping initMapping rowsByAtts
    header' = remove name header

buildTree :: DataSet -> Attribute -> AttSelector -> DecisionTree
buildTree dataset@(_, rows) c@(cName, _) select
  | null rows    = Null
  | allSame atts = Leaf (head atts)
  | otherwise    = Node name subTrees
  where
    att@(name, _) = nextAtt dataset c
    atts = map (lookUpAtt cName header) rows
    partition = partitionData dataset (select dataset c)
    subTrees = map (\(v, ds) -> (v, buildTree ds c select)) partition

--------------------------------------------------------------------
-- PART IV
--------------------------------------------------------------------

entropy :: DataSet -> Attribute -> Double
entropy dataset@(_, rows) attribute
  = sum (map (negate . xlogx) probs)
  where
    freqTable = buildFrequencyTable attribute dataset
    numRows = fromIntegral (length rows)
    probs = map ((/ numRows) . fromIntegral . snd) freqTable

gain :: DataSet -> Attribute -> Attribute -> Double
gain dataset@(_, rows) attribute classif
  = entropy dataset classif - sum (zipWith (*) probs entropies)
  where
    partition = partitionData dataset attribute
    freqTable = buildFrequencyTable attribute dataset
    numRows = fromIntegral (length rows)
    probs = map ((/ numRows) . fromIntegral . (`lookUp` freqTable) . fst) partition
    entropies = map ((`entropy` classif) . snd) partition

bestGainAtt :: AttSelector
bestGainAtt dataset@(header, _) classif@(cName, _)
  = snd (maximum (zip (map (\a -> gain dataset a classif) atts) atts))
  where
    atts = remove cName header

--------------------------------------------------------------------

outlook :: Attribute
outlook
  = ("outlook", ["sunny", "overcast", "rainy"])

temp :: Attribute
temp
  = ("temp", ["hot", "mild", "cool"])

humidity :: Attribute
humidity
  = ("humidity", ["high", "normal"])

wind :: Attribute
wind
  = ("wind", ["windy", "calm"])

result :: Attribute
result
  = ("result", ["good", "bad"])

fishingData :: DataSet
fishingData
  = (header, table)

header :: Header
table  :: [Row]
header
  =  [outlook,    temp,   humidity, wind,    result]
table
  = [["sunny",    "hot",  "high",   "calm",  "bad" ],
     ["sunny",    "hot",  "high",   "windy", "bad" ],
     ["overcast", "hot",  "high",   "calm",  "good"],
     ["rainy",    "mild", "high",   "calm",  "good"],
     ["rainy",    "cool", "normal", "calm",  "good"],
     ["rainy",    "cool", "normal", "windy", "bad" ],
     ["overcast", "cool", "normal", "windy", "good"],
     ["sunny",    "mild", "high",   "calm",  "bad" ],
     ["sunny",    "cool", "normal", "calm",  "good"],
     ["rainy",    "mild", "normal", "calm",  "good"],
     ["sunny",    "mild", "normal", "windy", "good"],
     ["overcast", "mild", "high",   "windy", "good"],
     ["overcast", "hot",  "normal", "calm",  "good"],
     ["rainy",    "mild", "high",   "windy", "bad" ]]

--
-- This is the same as the above table, but with the result in the second 
-- column...
--
fishingData' :: DataSet
fishingData'
  = (header', table')

header' :: Header
table'  :: [Row]
header'
  =  [outlook,    result, temp,   humidity, wind]
table'
  = [["sunny",    "bad",  "hot",  "high",   "calm"],
     ["sunny",    "bad",  "hot",  "high",   "windy"],
     ["overcast", "good", "hot",  "high",   "calm"],
     ["rainy",    "good", "mild", "high",   "calm"],
     ["rainy",    "good", "cool", "normal", "calm"],
     ["rainy",    "bad",  "cool", "normal", "windy"],
     ["overcast", "good", "cool", "normal", "windy"],
     ["sunny",    "bad",  "mild", "high",   "calm"],
     ["sunny",    "good", "cool", "normal", "calm"],
     ["rainy",    "good", "mild", "normal", "calm"],
     ["sunny",    "good", "mild", "normal", "windy"],
     ["overcast", "good", "mild", "high",   "windy"],
     ["overcast", "good", "hot",  "normal", "calm"],
     ["rainy",    "bad",  "mild", "high",   "windy"]]

fig1 :: DecisionTree
fig1
  = Node "outlook"
         [("sunny", Node "temp"
                         [("hot", Leaf "bad"),
                          ("mild",Node "humidity"
                                       [("high",   Leaf "bad"),
                                        ("normal", Leaf "good")]),
                          ("cool", Leaf "good")]),
          ("overcast", Leaf "good"),
          ("rainy", Node "temp"
                         [("hot", Null),
                          ("mild", Node "humidity"
                                        [("high",Node "wind"
                                                      [("windy",  Leaf "bad"),
                                                       ("calm", Leaf "good")]),
                                         ("normal", Leaf "good")]),
                          ("cool", Node "humidity"
                                        [("high", Null),
                                         ("normal", Node "wind"
                                                         [("windy",  Leaf "bad"),
                                                          ("calm", Leaf "good")])])])]

fig2 :: DecisionTree
fig2
  = Node "outlook"
         [("sunny", Node "humidity"
                         [("high", Leaf "bad"),
                          ("normal", Leaf "good")]),
          ("overcast", Leaf "good"),
          ("rainy", Node "wind"
                         [("windy", Leaf "bad"),
                          ("calm", Leaf "good")])]


outlookPartition :: Partition
outlookPartition
  = [("sunny",   ([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["hot","high","calm","bad"],["hot","high","windy","bad"],
                   ["mild","high","calm","bad"],["cool","normal","calm","good"],
                   ["mild","normal","windy","good"]])),
     ("overcast",([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["hot","high","calm","good"],["cool","normal","windy","good"],
                   ["mild","high","windy","good"],["hot","normal","calm","good"]])),
     ("rainy",   ([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["mild","high","calm","good"],["cool","normal","calm","good"],
                   ["cool","normal","windy","bad"],["mild","normal","calm","good"],
                   ["mild","high","windy","bad"]]))]