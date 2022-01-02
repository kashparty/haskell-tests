import Data.List
import Data.Maybe

type Id = String

type State = Int

type Transition = ((State, State), Id)

type LTS = [Transition]

type Alphabet = [Id]

data Process = STOP | Ref Id | Prefix Id Process | Choice [Process]
             deriving (Eq, Show)

type ProcessDef = (Id, Process)

type StateMap = [((State, State), State)]

------------------------------------------------------
-- PART I

lookUp :: Eq a => a -> [(a, b)] -> b
--Pre: The item is in the table
lookUp
  = (fromJust . ) . lookup

states :: LTS -> [State]
states lts
  = nub allStates
  where
    allStates = concatMap (\((a, b), _) -> [a, b]) lts

transitions :: State -> LTS -> [Transition]
transitions s lts
  = [((f, t), i) | ((f, t), i) <- lts, f == s]

alphabet :: LTS -> Alphabet
alphabet
  = nub . map snd

------------------------------------------------------
-- PART II

actions :: Process -> [Id]
actions STOP
  = []
actions (Ref _)
  = []
actions (Prefix i p)
  -- More efficient that nub
  | i `elem` pActions = pActions
  | otherwise         = i : pActions
  where
    pActions = actions p
actions (Choice ps)
  = (nub . concatMap actions) ps

accepts :: [Id] -> [ProcessDef] -> Bool
--Pre: The first item in the list of process definitions is
--     that of the start process.
accepts ids (p : ps)
  = accepts' ids (p : ps) p
  where
    accepts' :: [Id] -> [ProcessDef] -> ProcessDef -> Bool
    accepts' [] _ _
      = True
    accepts' ids ps (_, STOP)
      = False
    accepts' ids ps (_, Ref p)
      | p `elem` map fst ps = accepts' ids ps (p, lookUp p ps)
      | otherwise           = False
    accepts' (id : ids) ps (_, Prefix id' p)
      | id == id' = accepts' ids ps (id', p)
      | otherwise = False
    accepts' ids ps (_, Choice ps')
      = any (accepts' ids ps) (zip (repeat "") ps')

------------------------------------------------------
-- PART III

composeTransitions :: Transition -> Transition 
                   -> Alphabet -> Alphabet 
                   -> StateMap 
                   -> [Transition]
--Pre: The first alphabet is that of the LTS from which the first transition is
--     drawn; likewise the second.
--Pre: All (four) pairs of source and target states drawn from the two transitions
--     are contained in the given StateMap.
composeTransitions ((s, t), a) ((s', t'), a') a1 a2 sm 
  | a == a'         = [((ss', tt'), a)]
  | aInA2 && a'InA1 = []
  | a'InA1          = [((ss', ts'), a)]
  | aInA2           = [((ss', st'), a')]
  | otherwise       = [((ss', ts'), a), ((ss', st'), a')]
  where
    ss' = lookUp (s, s') sm
    st' = lookUp (s, t') sm
    ts' = lookUp (t, s') sm
    tt' = lookUp (t, t') sm
    aInA2 = a `elem` a2
    a'InA1 = a' `elem` a1

pruneTransitions :: [Transition] -> LTS
pruneTransitions ts
  = nub (visit 0 [])
  where
    visit :: State -> [State] -> [Transition]
    visit s vs
      | s `elem` vs = []
      | otherwise   = ts' ++ next
      where
        ts' = transitions s ts
        next = concatMap (\((f, t), _) -> visit t (f : vs)) ts'


------------------------------------------------------
-- PART IV

compose :: LTS -> LTS -> LTS
compose lts1 lts2
  = pruneTransitions allTrans
  where
    a1 = "$'" : alphabet lts1
    a2 = "$" : alphabet lts2
    ss = [(s, s') | s <- states lts1, s' <- states lts2]
    sm = zip ss [0..]
    tt (s, s') = [(t, t') | t <- ((s, s), "$") : transitions s lts1
                          , t' <- ((s', s'), "$'") : transitions s' lts2]
    composeTt (t, t') = composeTransitions t t' a1 a2 sm
    allTrans = concatMap (concatMap composeTt . tt) ss

------------------------------------------------------
-- PART V

buildLTS :: [ProcessDef] -> LTS
-- Pre: All process references (Ref constructor) have a corresponding
--      definition in the list of ProcessDefs.
buildLTS ps@((_, process) : _)
  = result 
  where
    (result, _, _) = buildLTS' process [] 0

    buildLTS' :: Process 
              -> [(Process, Int)] 
              -> Int 
              -> (LTS, [(Process, Int)], Int)
    buildLTS' STOP seen n
      = ([], seen, n)
    buildLTS' (Ref id') seen n
      = buildLTS' (lookUp id' ps) seen n
    buildLTS' p@(Prefix id (Ref id')) seen n
      | nextProcess `elem` map fst seen = ([((n, lookUp nextProcess seen), id)], 
                                           (p, n) : seen, n + 1)
      | otherwise                       = (((n, n + 1), id) : lts, seen', n')
      where
        nextProcess = lookUp id' ps
        (lts, seen', n') = buildLTS' nextProcess ((p, n) : seen) (n + 1)
    buildLTS' p@(Prefix id p') seen n
      | p' `elem` map fst seen = ([((n, lookUp p' seen), id)]
                                  , (p, n) : seen, n + 1)
      | otherwise              = (((n, n + 1), id) : lts, seen', n')
      where
        (lts, seen', n') = buildLTS' p' ((p, n) : seen) (n + 1)
    buildLTS' (Choice []) seen n
      = ([], seen, n)
    buildLTS' p@(Choice (p' : ps)) seen n
      = (lts ++ lts'', seen'', n'')
      where
        (lts, seen', n') = buildLTS' p' ((p, n) : seen) n
        (lts', seen'', n'') = buildLTS' (Choice ps) seen' (n' - 1)
        lts'' = map (\q@((f, t), i) -> if f == (n' - 1) 
                                       then ((n, t), i) 
                                       else q) lts'

------------------------------------------------------
-- Sample process definitions...

vendor, clock, play, maker, user, p, q, switch, off, on :: ProcessDef

vendor
  = ("VENDOR", Choice [Prefix "red"  (Prefix "coffee" (Ref "VENDOR")),
                       Prefix "blue" (Prefix "tea" (Ref "VENDOR")),
                       Prefix "off" STOP])

clock
  = ("CLOCK", Prefix "tick" (Prefix "tock" (Ref "CLOCK")))

play
  = ("PLAY", Choice [Prefix "think" (Prefix "move" (Ref "PLAY")),
                     Prefix "end" STOP])

maker
  = ("MAKER", Prefix "make" (Prefix "ready" (Ref "MAKER")))

user
  = ("USER",  Prefix "ready" (Prefix "use" (Ref "USER")))

p = ("P", Prefix "a" (Prefix "b" (Prefix "c" STOP)))

q = ("Q",  Prefix "d" (Prefix "c" (Prefix "b" (Ref "Q"))))

switch
  = ("SWITCH", Ref "OFF")

off
  = ("OFF", Choice [Prefix "on" (Ref "ON")])

on
  = ("ON",  Choice [Prefix "off" (Ref "OFF")])

------------------------------------------------------
-- Sample LTSs...

vendorLTS, clockLTS, playLTS, clockPlayLTS, makerLTS, userLTS, makerUserLTS,
  pLTS, qLTS, pqLTS, switchLTS :: LTS

vendorLTS
  = [((0,1),"off"),((0,2),"blue"),((0,3),"red"),((2,0),"tea"),((3,0),"coffee")]

clockLTS
  = [((0,1),"tick"),((1,0),"tock")]

playLTS
  = [((0,1),"end"),((0,2),"think"),((2,0),"move")]

clockPlayLTS
  = [((0,1),"end"),((1,4),"tick"),((4,1),"tock"),((0,3),"tick"),
     ((3,4),"end"),((3,0),"tock"),((3,5),"think"),((5,3),"move"),
     ((5,2),"tock"),((2,0),"move"),((2,5),"tick"),((0,2),"think")]

makerLTS
  = [((0,1),"make"),((1,0),"ready")]

userLTS
  = [((0,1),"ready"),((1,0),"use")]

makerUserLTS
  = [((0,2),"make"),((2,1),"ready"),((1,0),"use"),((1,3),"make"),((3,2),"use")]

pLTS
  = [((0,1),"a"),((1,2),"b"),((2,3),"c")]

qLTS
  = [((0,1),"d"),((1,2),"c"),((2,0),"b")]

pqLTS
  = [((0,1),"d"),((1,4),"a"),((0,3),"a"),((3,4),"d")]

switchLTS
  = [((0,1),"on"),((1,0),"off")]
