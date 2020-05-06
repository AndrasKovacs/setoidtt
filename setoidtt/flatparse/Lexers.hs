{-# language Strict #-}

module Lexers where

import Control.Applicative
import Control.Monad.State
import Data.IntMap.Strict (IntMap)
import Data.IntSet (IntSet)
import Data.Set (Set)
import Data.Map.Strict (Map)
import Data.String
import Lens.Micro.Platform
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S

-- import Debug.Trace

data Regex
  = Eps
  | Char Char
  | Regex :*: Regex
  | Regex :|: Regex
  | Star Regex
  deriving (Eq, Show)

infixr 4 :|:
infixr 5 :*:

instance IsString Regex where
  fromString = go where
    go []     = Eps
    go [c]    = Char c
    go (c:cs) = Char c :*: go cs

type Rules = [Regex]
type Predicate = Char
type RuleId = Int
type StateId = Int
type StateSet  = IntSet

data NNode = NNode {
  nNodeAccept :: Maybe RuleId,      -- ^ Accepting a rule.
  nNodeEps    :: StateSet,          -- ^ Epsilon transition.
  nNodeNext   :: Map Char StateSet  -- ^ Char transition.
  }
makeFields ''NNode

instance Show NNode where
  show (NNode acc eps nxt) =
    show (acc, IS.toList eps, (IS.toList <$>) <$> M.toList nxt)

type NFAStates = IntMap NNode
type NFAM      = State (Int, NFAStates)

newState :: NFAM StateId
newState = do
  i <- _1 <<%= (+1)
  _2 %= IM.insert i (NNode Nothing mempty mempty)
  pure i

charEdge :: Char -> StateId -> StateId -> NFAM ()
charEdge c from to = _2 %= IM.adjust (next %~ M.alter go c) from where
  go = Just . maybe (IS.singleton to) (IS.insert to)

epsilonEdge :: StateId -> StateId -> NFAM ()
epsilonEdge from to = _2 %= IM.adjust (eps %~ IS.insert to) from

regex2nfa :: StateId -> StateId -> Regex -> NFAM ()
regex2nfa b e = \case
  Eps       -> epsilonEdge b e
  Char c    -> charEdge c b e
  r1 :*: r2 -> do {s <- newState; regex2nfa b s r1; regex2nfa s e r2}
  r1 :|: r2 -> do {regex2nfa b e r1; regex2nfa b e r2}
  Star r    -> do {s <- newState; epsilonEdge b s; regex2nfa s s r; epsilonEdge s e}

data NFA = NFA {
  nFAStates :: NFAStates,
  nFAStart  :: StateId
  } deriving Show

rules2nfa :: Rules -> NFA
rules2nfa rules = (`evalState` (0, mempty)) do
  start <- newState
  forM_ (zip [0..] rules) \(i, r) -> do
    acc <- newState
    _2 %= IM.adjust (accept .~ Just i) acc
    regex2nfa start acc r
    pure acc
  NFA <$> use _2 <*> pure start

data DNode = DNode {
  dNodeAccept :: Maybe RuleId,
  dNodeNext   :: Map Char StateId
  }
makeFields ''DNode

instance Show DNode where
  show (DNode acc next) = show (acc, M.toList next)

type DFAStates = IntMap DNode

data DFA = DFA {
  dFAStates :: DFAStates,
  dFAStart  :: StateId
  } deriving Show

nfa2dfa :: NFA -> DFA
nfa2dfa (NFA nfa start) = DFA dfa (visited M.! start') where

  start' = epsClosure start
  (_, visited, dfa) = execState (go start') (0, mempty, mempty)

  epsClosure :: StateId -> StateSet
  epsClosure s = go (mempty @StateSet) s where
    go ss s | IS.member s ss = ss
    go ss s = IS.foldl' go (IS.insert s ss) ((nfa IM.! s)^.eps)

  epsClosures :: StateSet -> StateSet
  epsClosures = IS.foldl' (\ss s -> ss <> epsClosure s) mempty

  transitions :: StateSet -> Map Char StateSet
  transitions = IS.foldl' (\trans s -> M.unionWith (<>) trans ((nfa IM.! s)^.next)) mempty

  accepts :: StateSet -> Maybe RuleId
  accepts = IS.foldl' go Nothing where
    go acc s = case (acc, (nfa IM.! s)^.accept) of
      (Just a, Just b) -> Just (min a b)
      (a, b)           -> a <|> b

  -- input has to be epsilon-closed
  go :: StateSet -> State (Int, Map StateSet Int, DFAStates) StateId
  go ss =
    (M.lookup ss <$> use _2) >>= \case
      Just s  -> pure s
      Nothing -> do
        (nextId, visited, dfa) <- get
        put (nextId+1, M.insert ss nextId visited, dfa)
        next <- traverse (go . epsClosures) (transitions ss)
        modify (_3 %~ IM.insert nextId (DNode (accepts ss) next))
        pure nextId


minimize :: DFA -> DFA
minimize (DFA dfa start) = DFA minimized (ren start) where

  prepartition :: Set StateSet
  prepartition = S.fromList $ M.elems $
    IM.foldlWithKey'
      (\m s node ->
         M.alter (Just . maybe (IS.singleton s) (IS.insert s))
                 (node^.accept) m)
      mempty dfa

  eqvGroups :: Set StateSet
  eqvGroups = go (prepartition, prepartition)

  renaming :: IntMap StateId
  renaming = IM.fromList [(s, s') | (s', ss) <- zip [0..] (S.toList eqvGroups),
                                    s        <- IS.toList ss]

  ren :: StateId -> StateId
  ren = (renaming IM.!)

  minimized :: DFAStates
  minimized = IM.fromList
    [(s', (dfa IM.! s) & next %~ fmap ren) |
     (s', s) <- zip [0..] (head . IS.toList <$> S.toList eqvGroups)]

  presetMap :: IntMap (Map Char StateSet)
  presetMap =
    IM.foldlWithKey'
      (\m s node ->
         M.foldlWithKey'
           (\m c s' ->
             IM.alter
               (Just . maybe (M.singleton c (IS.singleton s))
                             (M.alter (Just . maybe (IS.singleton s) (IS.insert s)) c))
               s' m)
           m (node^.next))
      mempty dfa

  minStateSet :: StateSet -> StateSet -> StateSet
  minStateSet s s' = if IS.size s < IS.size s' then s else s'

  go :: (Set StateSet, Set StateSet) -> Set StateSet
  go (p, q) = case S.minView q of
    Nothing     -> p
    Just (a, q) ->

      let presets :: Map Char StateSet
          presets = IS.foldl'
            (\cmap s -> maybe cmap (M.unionWith (<>) cmap) (IM.lookup s presetMap))
            mempty a

      in go $ M.foldlWithKey'
                (\(!p, !q) c x ->
                   S.foldl'
                     (\(!p, !q) y ->
                        let xandy = IS.intersection x y in
                        let yminusx = IS.difference y x in
                        if IS.null xandy || IS.null yminusx then
                          (p, q)
                        else
                          let p' = S.insert xandy $ S.insert yminusx $ S.delete y p in
                          if S.member y q then
                            (p', S.insert xandy $ S.insert yminusx $ S.delete y q)
                          else
                            (p', S.insert (minStateSet xandy yminusx) q)
                        )
                     (p, q) p)
                (p, q) presets
