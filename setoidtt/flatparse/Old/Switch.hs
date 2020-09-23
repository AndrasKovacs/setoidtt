
module Old.Switch where

import Control.Monad
import Data.Foldable
import Data.Map.Strict (Map)
import Old.FlatParse
import GHC.Word
import qualified Data.Map.Strict as M
import Language.Haskell.TH

data Trie a = Branch !a !(Map Word8 (Trie a))
  deriving Show

type Rule = Maybe Int

nilTrie :: Trie Rule
nilTrie = Branch Nothing mempty

updRule :: Int -> Maybe Int -> Maybe Int
updRule rule = Just . maybe rule (min rule)

insert :: Int -> [Word8] -> Trie Rule -> Trie Rule
insert rule = go where
  go [] (Branch rule' ts) =
    Branch (updRule rule rule') ts
  go (c:cs) (Branch rule' ts) =
    Branch rule' (M.alter (Just . maybe (go cs nilTrie) (go cs)) c ts)

fromList :: [(Int, String)] -> Trie Rule
fromList = foldl' (\t (r, s) -> insert r (charToBytes =<< s) t) nilTrie

-- | Decorate a trie with the minimum lengths of non-empty paths. This
--   is used later to place `ensureBytes#`.
mindepths :: Trie Rule -> Trie (Rule, Int)
mindepths (Branch rule ts) =
  if M.null ts then
    Branch (rule, 0) mempty
  else
    let !ts' = M.map mindepths ts in
    Branch (
      rule,
      minimum (M.map (\(Branch (rule,d) _) -> maybe (d + 1) (\_ -> 1) rule) ts'))
      ts'

data Trie' a
  = Branch' !a !(Map Word8 (Trie' a))
  | Path !a ![Word8] !(Trie' a)
  deriving Show

-- | Compress linear paths.
pathify :: Trie (Rule, Int) -> Trie' (Rule, Int)
pathify (Branch a ts) = case M.toList ts of
  [] -> Branch' a mempty
  [(w, t)] -> case pathify t of
           Path (Nothing, _) ws t -> Path a (w:ws) t
           t                      -> Path a [w] t
  _   -> Branch' a (M.map pathify ts)

fallbacks :: Trie' (Rule, Int) -> Trie' (Rule, Int, Int)
fallbacks = go Nothing 0  where
  go :: Rule -> Int -> Trie' (Rule, Int) -> Trie' (Rule, Int, Int)
  go !rule !n (Branch' (rule', d) ts)
    | M.null ts        = Branch' (rule', 0, d) mempty
    | Nothing <- rule' = Branch' (rule, n, d) (go rule (n + 1) <$> ts)
    | otherwise        = Branch' (rule, n, d) (go rule' 1      <$> ts)
  go rule n (Path (rule', d) ws t)
    | Nothing <- rule' = Path (rule, n, d)  ws (go rule (n + 1) t)
    | otherwise        = Path (rule', 0, d) ws (go rule' (length ws) t)

-- | Decorate with `ensureBytes#` invocations, represented as
--   `Maybe Int`.
ensureBytes :: Trie' (Rule, Int, Int) -> Trie' (Rule, Int, Maybe Int)
ensureBytes = go 0 where
  go :: Int -> Trie' (Rule, Int, Int) -> Trie' (Rule, Int, Maybe Int)
  go res = \case
    Branch' (r, n, d) ts
      | M.null ts -> Branch' (r, n, Nothing) mempty
      |  res < 1  -> Branch' (r, n, Just d ) (go (d   - 1) <$> ts)
      | otherwise -> Branch' (r, n, Nothing) (go (res - 1) <$> ts)
    Path (r, n, d) ws t -> case length ws of
      l | res < l   -> Path (r, n, Just $! d - res) ws (go (d - l)   t)
        | otherwise -> Path (r, n, Nothing        ) ws (go (res - l) t)

compileTrie :: [(Int, String)] -> Trie' (Rule, Int, Maybe Int)
compileTrie = ensureBytes . fallbacks . pathify . mindepths . fromList

genTrie :: (Map (Maybe Int) Exp, Trie' (Rule, Int, Maybe Int)) -> Q Exp
genTrie (rules, t) = do
  branches <- traverse (\e -> (,) <$> (newName "rule") <*> pure e) rules

  let ix m k = case M.lookup k m of
        Nothing -> error ("key not in map: " ++ show k)
        Just a  -> a

  let ensure :: Maybe Int -> Maybe (Q Exp)
      ensure = fmap (\n -> [| ensureBytes# n |])

      fallback :: Rule -> Int ->  Q Exp
      fallback rule 0 = pure $ VarE $ fst $ ix branches rule
      fallback rule n = [| setBack# n >> $(pure $ VarE $ fst $ ix branches rule) |]

  let go :: Trie' (Rule, Int, Maybe Int) -> Q Exp
      go = \case
        Branch' (r, n, alloc) ts
          | M.null ts -> pure $ VarE $ fst $ branches M.! r
          | otherwise -> do
              next   <- (traverse . traverse) go (M.toList ts)
              fallb  <- fallback r (n + 1)
              alloc  <- maybe (pure []) (fmap $ \e -> [NoBindS e]) (ensure alloc)
              pure $ DoE $
               alloc ++
               [BindS (VarP (mkName "c")) (VarE 'scanAny8#),
                NoBindS (CaseE (VarE (mkName "c"))
                   (map (\(w, t) ->
                           Match (LitP (IntegerL (fromIntegral w)))
                                 (NormalB t)
                                 [])
                        next
                    ++ [Match WildP (NormalB fallb) []]))]
        Path (r, n, alloc) ws t ->
          case ensure alloc of
            Nothing    -> [| br $(scanBytes# False ws) $(go t) $(fallback r n)|]
            Just alloc -> [| $alloc >> br $(scanBytes# False ws) $(go t) $(fallback r n) |]

  letE
    (map (\(x, rhs) -> valD (varP x) (normalB (pure rhs)) []) (toList branches))
    (go t)

parseSwitch :: Q Exp -> Q ([(String, Exp)], Maybe Exp)
parseSwitch exp = exp >>= \case
  CaseE (UnboundVarE _) []    -> error "switch: empty clause list"
  CaseE (UnboundVarE _) cases -> do
    (cases, last) <- pure (init cases, last cases)
    cases <- forM cases \case
      Match (LitP (StringL str)) (NormalB rhs) [] -> pure (str, rhs)
      _ -> error "switch: expected a match clause on a string literal"
    (cases, last) <- case last of
      Match (LitP (StringL str)) (NormalB rhs) [] -> pure (cases ++ [(str, rhs)], Nothing)
      Match WildP                (NormalB rhs) [] -> pure (cases, Just rhs)
      _ -> error "switch: expected a match clause on a string literal or a wildcard"
    pure (cases, last)
  _ -> error "switch: expected a \"case _ of\" expression"

genSwitchTrie :: ([(String, Exp)], Maybe Exp) -> (Map (Maybe Int) Exp, Trie' (Rule, Int, Maybe Int))
genSwitchTrie (cases, fallback) =

  let (branches, strings) = unzip do
        (i, (str, rhs)) <- zip [0..] cases
        pure ((Just i, rhs), (i, str))

  in ( M.fromList ((Nothing, maybe (VarE 'empty) id fallback) : branches)
     , compileTrie strings)

switch :: Q Exp -> Q Exp
switch exp = genTrie =<< (genSwitchTrie <$> parseSwitch exp)
