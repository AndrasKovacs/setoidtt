
module FlatParseIndent where

import qualified Data.ByteString as B
import qualified Data.ByteString.Short.Internal as SB
import qualified Data.ByteString.Unsafe as B
import qualified Data.Text.Short as T
import qualified Data.Text.Short.Unsafe as T
import qualified Data.Map.Strict as M

import Data.Map (Map)
import Data.Bits
import Data.Char (ord)
import Data.Foldable
import Data.Word
import GHC.Exts
import GHC.Word
import Language.Haskell.TH
import System.IO.Unsafe

--------------------------------------------------------------------------------

data Error e = Default | Custom e
  deriving Show

type Res# e a = (# (# a, Addr#, Int# #) | (# Error e, Addr# #) #)

pattern OK# :: a -> Addr# -> Int# -> Res# e a
pattern OK# a s j = (# (# a, s, j #) | #)

pattern Err# :: Error e -> Addr# -> Res# e a
pattern Err# e s = (# | (# e, s #) #)
{-# complete OK#, Err# #-}

newtype Parser e a = Parser {runParser# :: Addr# -> Int# -> Addr# -> Int# -> Res# e a}

instance Functor (Parser e) where
  fmap f (Parser g) = Parser \e i s j -> case g e i s j of
    OK# a s j  -> let !b = f a in OK# b s j
    Err# e s -> Err# e s
  {-# inline fmap #-}

  (<$) a' (Parser g) = Parser \e i s j -> case g e i s j of
    OK# a s j -> OK# a' s j
    Err# e s  -> Err# e s
  {-# inline (<$) #-}

err :: e -> Parser e a
err e = Parser \_ i s j -> Err# (Custom e) s
{-# inline err #-}

empty :: Parser e a
empty = Parser \e i s j -> Err# Default s
{-# inline empty #-}

instance Applicative (Parser e) where
  pure a = Parser \e i s j -> OK# a s j
  {-# inline pure #-}
  Parser ff <*> Parser fa = Parser \e i s j -> case ff e i s j of
    Err# e s -> Err# e s
    OK# f s j -> case fa e i s j of
      Err# e s  -> Err# e s
      OK# a s j -> OK# (f a) s j
  {-# inline (<*>) #-}
  Parser fa <* Parser fb = Parser \e i s j -> case fa e i s j of
    Err# e s  -> Err# e s
    OK# a s j -> case fb e i s j of
      Err# e s  -> Err# e s
      OK# b s j -> OK# a s j
  {-# inline (<*) #-}
  Parser fa *> Parser fb = Parser \e i s j -> case fa e i s j of
    Err# e s  -> Err# e s
    OK# a s j -> fb e i s j
  {-# inline (*>) #-}

instance Monad (Parser e) where
  return = pure
  {-# inline return #-}
  Parser fa >>= f = Parser \e i s j -> case fa e i s j of
    Err# e s  -> Err# e s
    OK# a s j -> runParser# (f a) e i s j
  {-# inline (>>=) #-}
  Parser fa >> Parser fb = Parser \e i s j -> case fa e i s j of
    Err# e s  -> Err# e s
    OK# a s j -> fb e i s j
  {-# inline (>>) #-}

ask :: Parser e Int
ask = Parser \e i s j -> OK# (I# i) s j
{-# inline ask #-}

local :: (Int -> Int) -> Parser e a -> Parser e a
local f (Parser fa) = Parser \e i s j -> case f (I# i) of
  I# i -> fa e i s j
{-# inline local #-}

derefChar8# :: Addr# -> Char#
derefChar8# addr = indexCharOffAddr# addr 0#
{-# inline derefChar8# #-}

eof :: Parser e ()
eof = Parser \e i s j -> case eqAddr# e s of
  1# -> OK# () s j
  _  -> Err# Default s
{-# inline eof #-}

isDigit :: Char -> Bool
isDigit c = '0' <= c && c <= '9'
{-# inline isDigit #-}

isLatinLetter :: Char -> Bool
isLatinLetter c = ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
{-# inline isLatinLetter #-}

isGreekLetter :: Char -> Bool
isGreekLetter c = ('Α' <= c && c <= 'Ω') || ('α' <= c && c <= 'ω')
{-# inline isGreekLetter #-}

-- | Choose between two parsers. The second parser is tried if the first one
--   fails, regardless of how much input the first parser consumed.
infixr 6 <!>
(<!>) :: Parser e a -> Parser e a -> Parser e a
(<!>) (Parser f) (Parser g) = Parser \e i s j ->
  case f e i s j of
    Err# _ _ -> g e i s j
    x        -> x
{-# inline (<!>) #-}

-- | Choose between two parsers. The second parser is only tried
--   if the first one fails without having consumed input.
infixr 6 <|>
(<|>) :: Parser e a -> Parser e a -> Parser e a
(<|>) (Parser f) (Parser g) = Parser \e i s j ->
  case f e i s j of
    Err# err s' -> case eqAddr# s s' of
                     1# -> g e i s j
                     _  -> Err# err s'
    x         -> x
{-# inline (<|>) #-}

-- | Reset the input position if the given parser fails.
try :: Parser e a -> Parser e a
try (Parser f) = Parser \e i s j -> case f e i s j of
  Err# err _ -> Err# err s
  x          -> x
{-# inline try #-}

-- | Parse any `Char` in the ASCII range.
anyCharA :: Parser e Char
anyCharA = Parser \e i s j -> case eqAddr# e s of
  1# -> Err# Default s
  _  -> case derefChar8# s of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# s 1#) j
      _  -> Err# Default s
{-# inline anyCharA #-}

-- | Skip any `Char` in the ASCII range.
anyCharA_ :: Parser e ()
anyCharA_ = () <$ anyCharA
{-# inline anyCharA_ #-}

-- | Parse any `Char`.
--   Assumes that input is UTF8!
anyChar :: Parser e Char
anyChar = Parser \e i s j -> case eqAddr# e s of
  1# -> Err# Default s
  _  -> case derefChar8# s of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# s 1#) j
      _  -> case eqAddr# e (plusAddr# s 1#) of
        1# -> Err# Default s
        _  -> case indexCharOffAddr# s 1# of
          c2 -> case c1 `leChar#` '\xDF'# of
            1# ->
              let resc = ((ord# c1 -# 0xC0#) `uncheckedIShiftL#` 6#) `orI#`
                          (ord# c2 -# 0x80#)
              in OK# (C# (chr# resc)) (plusAddr# s 2#) j
            _ -> case eqAddr# e (plusAddr# s 2#) of
              1# -> Err# Default s
              _  -> case indexCharOffAddr# s 2# of
                c3 -> case c1 `leChar#` '\xEF'# of
                  1# ->
                    let resc = ((ord# c1 -# 0xE0#) `uncheckedIShiftL#` 12#) `orI#`
                               ((ord# c2 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                                (ord# c3 -# 0x80#)
                    in OK# (C# (chr# resc)) (plusAddr# s 3#) j
                  _ -> case eqAddr# e (plusAddr# s 3#) of
                    1# -> Err# Default s
                    _  -> case indexCharOffAddr# s 3# of
                      c4 ->
                        let resc = ((ord# c1 -# 0xF0#) `uncheckedIShiftL#` 18#) `orI#`
                                   ((ord# c2 -# 0x80#) `uncheckedIShiftL#` 12#) `orI#`
                                   ((ord# c3 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                                    (ord# c4 -# 0x80#)
                        in OK# (C# (chr# resc)) (plusAddr# s 4#) j
{-# inline anyChar #-}

-- | Skip any `Char`.
anyChar_ :: Parser e ()
anyChar_ = Parser \e i s j -> case eqAddr# e s of
  1# -> Err# Default s
  _  -> case derefChar8# s of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# () (plusAddr# s 1#) j
      _  ->
        let s' =
              case c1 `leChar#` '\xDF'# of
                1# -> plusAddr# s 2#
                _  -> case c1 `leChar#` '\xEF'# of
                    1# -> plusAddr# s 3#
                    _ ->  plusAddr# s 4#
        in case leAddr# s' e of
             1# -> OK# () s' j
             _  -> Err# Default s
{-# inline anyChar_ #-}

-- | Parser a `Char` for which a predicate holds.
satisfy :: (Char -> Bool) -> Parser e Char
satisfy f = Parser \e i s j -> case runParser# anyChar e i s j of
  OK# c s j | f c -> OK# c s j
  OK# c _ _       -> Err# Default s
  Err# e s        -> Err# e s
{-#  inline satisfy #-}

-- | Parse an ASCII `Char` for which a predicate holds.
satisfyA :: (Char -> Bool) -> Parser e Char
satisfyA f = Parser \e i s j -> case runParser# anyCharA e i s j of
  OK# c s j | f c -> OK# c s j
  OK# c _ _       -> Err# Default s
  Err# e s        -> Err# e s
{-#  inline satisfyA #-}

-- | Skip a parser zero or more times. This fails if the given parser fails with
--   having consumed input.
many_ :: Parser e a -> Parser e ()
many_ (Parser f) = go where
  go = Parser \e i s j -> case f e i s j of
    Err# e s' -> case eqAddr# s s' of
                   1# -> OK# () s j
                   _  -> Err# e s'
    OK# a s j -> runParser# go e i s j
{-# inline many_ #-}

manyBr_ :: Parser e a -> Parser e b -> Parser e ()
manyBr_ pa pb = go where
  go = br pa (pb >> go) (pure ())
{-# inline manyBr_ #-}

manyTok_ :: Parser e a -> Parser e ()
manyTok_ (Parser f) = go where
  go = Parser \e i s j -> case f e i s j of
    Err# _ _  -> OK# () s j
    OK# a s j -> runParser# go e i s j
{-# inline manyTok_ #-}

-- | Skip a parser one or more times. This fails if the given parser fails with
--   having consumed input.
some_ :: Parser e a -> Parser e ()
some_ pa = pa >> many_ pa
{-# inline some_ #-}

someBr_ :: Parser e a -> Parser e b -> Parser e ()
someBr_ pa pb = pa >> pb >> manyBr_ pa pb
{-# inline someBr_ #-}

someTok_ :: Parser e a -> Parser e ()
someTok_ pa = pa >> manyTok_ pa
{-# inline someTok_ #-}

-- | Skip a parser zero or more times until a closing parser. This fails
--   if the closing parser fails with having consumed input.
manyTill_ :: Parser e a -> Parser e b -> Parser e ()
manyTill_ pa end = go where
  go = (() <$ end) <|> (pa >> go)
{-# inline manyTill_ #-}

chainl :: (b -> a -> b) -> Parser e b -> Parser e a -> Parser e b
chainl f start elem = start >>= go where
  go b = do {!a <- elem; go $! f b a} <|> pure b
{-# inline chainl #-}

chainr :: (a -> b -> b) -> Parser e a -> Parser e b -> Parser e b
chainr f elem end = go where
  go = (f <$> elem <*> go) <|> end
{-# inline chainr #-}

silent :: Parser e a -> Parser e a
silent pa = Parser \e i s j -> case runParser# pa e i s j of
  Err# e s -> Err# Default s
  x        -> x
{-# inline silent #-}

data Pos = Pos Addr#

instance Eq Pos where
  Pos p == Pos p' = isTrue# (eqAddr# p p')
  {-# inline (==) #-}

data Span = Span !Pos !Pos
  deriving Eq

spanned :: Parser e a -> Parser e (a, Span)
spanned (Parser f) = Parser \e i s j -> case f e i s j of
  Err# e s    -> Err# e s
  OK# a s' j' -> OK# (a, Span (Pos s) (Pos s')) s' j'
{-# inline spanned #-}

spanToShortText :: Span -> T.ShortText
spanToShortText (Span (Pos start) (Pos end)) =
  let len  = minusAddr# end start
  in T.fromShortByteStringUnsafe (SB.SBS (runRW# \s ->
       case newByteArray# len s of
         (# s, marr #) -> case copyAddrToByteArray# start marr 0# len s of
           s -> case unsafeFreezeByteArray# marr s of
             (# s, arr #) -> arr))
{-# inline spanToShortText #-}

asShortText :: Parser e a -> Parser e (T.ShortText)
asShortText p = fmap (\(_ ,s) -> spanToShortText s) (spanned p)
{-# inline asShortText #-}

getPos :: Parser e Pos
getPos = Parser \e i s j -> OK# (Pos s) s j
{-# inline getPos #-}

setPos :: Pos -> Parser e ()
setPos (Pos s) = Parser \e i _ j -> OK# () s j
{-# inline setPos #-}

data PosInfo = PosInfo {
  _lineNum :: !Int,
  _colNum  :: !Int,
  _line    :: {-# unpack #-} !(B.ByteString)
  } deriving Show

-- | Retrieve line and column informations for a list of `Pos`-s.  Throw an
--   error if any of the positions does not point into the `ByteString`.
posInfo :: B.ByteString -> [Pos] -> [PosInfo]
posInfo = error "TODO"

-- | Run a parser in a given span. The span behaves as the new beginning and end
--   of the input buffer. The `Int` parameter is the current indentation level
--   at the beginning of the spane. When the parser finishes, the original
--   external state is restored.
inSpan :: Int -> Span -> Parser e a -> Parser e a
inSpan (I# j) (Span (Pos start) (Pos end)) (Parser f) =
  Parser \e' i s' j' -> case f end i start j of
    OK# a _ _  -> OK# a s' j'
    Err# err _ -> Err# err s'
{-# inline inSpan #-}

data Result e a = OK a B.ByteString | Err (Error e) B.ByteString
  deriving Show

runParser :: Parser e a -> B.ByteString -> Result e a
runParser (Parser f) b = unsafeDupablePerformIO do
  B.unsafeUseAsCString b \(Ptr buf) -> do
    let !(I# len) = B.length b
    let end = plusAddr# buf len
    case f end 0# buf 0# of
      Err# e s  -> do
        let offset = minusAddr# s buf
        pure (Err e (B.drop (I# offset) b))
      OK# a s j -> do
        let offset = minusAddr# s buf
        pure (OK a (B.drop (I# offset) b))

testParser :: Parser e a -> String -> Result e a
testParser pa s = runParser pa (B.pack (concatMap charToBytes s))

br :: Parser e a -> Parser e b -> Parser e b -> Parser e b
br pa pt pf = Parser \e i s j -> case runParser# pa e i s j of
  OK# _ s j -> runParser# pt e i s j
  Err# _ _  -> runParser# pf e i s j
{-# inline br #-}

get :: Parser e Int
get = Parser \e i s j -> OK# (I# j) s j
{-# inline get #-}

put :: Int -> Parser e ()
put (I# j) = Parser \e i s _ -> OK# () s j
{-# inline put #-}

modify :: (Int -> Int) -> Parser e ()
modify f = Parser \e i s j -> case f (I# j) of
  I# j -> OK# () s j
{-# inline modify #-}

-- char and string
--------------------------------------------------------------------------------

charToBytes :: Char -> [Word8]
charToBytes c'
    | c <= 0x7f     = [fromIntegral c]
    | c <= 0x7ff    = [0xc0 .|. y, 0x80 .|. z]
    | c <= 0xffff   = [0xe0 .|. x, 0x80 .|. y, 0x80 .|. z]
    | c <= 0x10ffff = [0xf0 .|. w, 0x80 .|. x, 0x80 .|. y, 0x80 .|. z]
    | otherwise = error "Not a valid Unicode code point"
  where
    c = ord c'
    z = fromIntegral (c                 .&. 0x3f)
    y = fromIntegral (unsafeShiftR c 6  .&. 0x3f)
    x = fromIntegral (unsafeShiftR c 12 .&. 0x3f)
    w = fromIntegral (unsafeShiftR c 18 .&. 0x7)

strToBytes :: String -> [Word8]
strToBytes = concatMap charToBytes
{-# inline strToBytes #-}

packBytes :: [Word8] -> Word
packBytes = fst . foldl' go (0, 0) where
  go (acc, shift) w | shift == 64 = error "packWords: too many bytes"
  go (acc, shift) w = (unsafeShiftL (fromIntegral w) shift .|. acc, shift+8)

splitBytes :: [Word8] -> ([Word8], [Word])
splitBytes ws = case quotRem (length ws) 8 of
  (0, _) -> (ws, [])
  (_, r) -> (as, chunk8s bs) where
              (as, bs) = splitAt r ws
              chunk8s [] = []
              chunk8s ws = let (as, bs) = splitAt 8 ws in
                           packBytes as : chunk8s bs

scanAny8# :: Parser e Word8
scanAny8# = Parser \e i s j -> OK# (W8# (indexWord8OffAddr# s 0#)) (plusAddr# s 1#) j
{-# inline scanAny8# #-}

scan8# :: Word -> Parser e ()
scan8# (W# c) = Parser \e i s j ->
  case indexWord8OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 1#) j
      _  -> Err# Default s
{-# inline scan8# #-}

scan16# :: Word -> Parser e ()
scan16# (W# c) = Parser \e i s j ->
  case indexWord16OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 2#) j
      _  -> Err# Default s
{-# inline scan16# #-}

scan32# :: Word -> Parser e ()
scan32# (W# c) = Parser \e i s j ->
  case indexWord32OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 4#) j
      _  -> Err# Default s
{-# inline scan32# #-}

scan64# :: Word -> Parser e ()
scan64# (W# c) = Parser \e i s j ->
  case indexWord64OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 8#) j
      _  -> Err# Default s
{-# inline scan64# #-}

scanPartial64# :: Int -> Word -> Parser e ()
scanPartial64# (I# len) (W# w) = Parser \e i s j ->
  case indexWordOffAddr# s 0# of
    w' -> case uncheckedIShiftL# (8# -# len) 3# of
      sh -> case uncheckedShiftL# w' sh of
        w' -> case uncheckedShiftRL# w' sh of
          w' -> case eqWord# w w' of
            1# -> OK# () (plusAddr# s len) j
            _  -> Err# Default s
{-# inline scanPartial64# #-}

ensureBytes# :: Int -> Parser e ()
ensureBytes# (I# len) = Parser \e i s j ->
  case len <=# minusAddr# e s of
    1# -> OK# () s j
    _  -> Err# Default s
{-# inline ensureBytes# #-}

scanBytes# :: Bool -> [Word8] -> Q Exp
scanBytes# isToken bytes = do
  let !(leading, w8s) = splitBytes bytes
      !leadingLen     = length leading
      !w8sLen         = length w8s
      !scanw8s        = go w8s where
                         go (w8:[] ) = [| scan64# w8 |]
                         go (w8:w8s) = [| scan64# w8 >> $(go w8s) |]
                         go []       = [| pure () |]
  case w8s of
    [] -> if elem leadingLen [3, 5, 6, 7] && isToken
             then [| try $(go leading) |]
             else [| $(go leading) |]
          where
            go (a:b:c:d:[]) = let !w = packBytes [a, b, c, d] in [| scan32# w |]
            go (a:b:c:d:ws) = let !w = packBytes [a, b, c, d] in [| scan32# w >> $(go ws) |]
            go (a:b:[])     = let !w = packBytes [a, b]       in [| scan16# w |]
            go (a:b:ws)     = let !w = packBytes [a, b]       in [| scan16# w >> $(go ws) |]
            go (a:[])       = [| scan8# a |]
            go []           = [| pure () |]
    _  -> case leading of

      [] | w8sLen /= 1 && isToken -> [| try $scanw8s |]
         | otherwise              -> [| $scanw8s     |]

      [a] | isToken   -> [| try (scan8# a >> $scanw8s) |]
          | otherwise -> [| scan8# a >> $scanw8s |]

      ws  -> let !w = packBytes ws
                 !l = length ws
             in if isToken then [| try (scanPartial64# l w >> $scanw8s) |]
                           else [| scanPartial64# l w >> $scanw8s |]

string :: String -> Q Exp
string str = do
  let !bytes = strToBytes str
      !len   = length bytes
  [| ensureBytes# len >> $(scanBytes# True bytes) |]

char :: Char -> Q Exp
char c = string [c]

-- Word sets
--------------------------------------------------------------------------------

data Trie a = Branch !Bool !a !(Map Word8 (Trie a))
  deriving Show

nilTrie :: Trie ()
nilTrie = Branch False () mempty

insert :: [Word8] -> Trie () -> Trie ()
insert []     (Branch _ d ts) = Branch True d ts
insert (c:cs) (Branch b d ts) =
  Branch b d (M.alter (Just . maybe (insert cs nilTrie) (insert cs)) c ts)

fromList :: [String] -> Trie ()
fromList = foldl' (\t s -> insert (charToBytes =<< s) t) nilTrie

mindepths :: Trie () -> Trie Int
mindepths (Branch b _ ts) =
  if M.null ts then
    Branch b 0 mempty
  else
    let ts' = M.map mindepths ts in
    Branch b (minimum (M.map (\(Branch b d _) -> if b then 1 else d + 1) ts'))
           ts'

data Trie' = Branch' !Bool !Int !(Map Word8 Trie')
           | Path !Bool !Int ![Word8] !Trie'
  deriving Show

pathify :: Trie Int -> Trie'
pathify (Branch b d ts) = case M.toList ts of
  []       -> Branch' b d mempty
  [(w, t)] -> case pathify t of
           Path False _ ws t -> Path b d (w:ws) t
           t                 -> Path b d [w] t
  _   -> Branch' b d (M.map pathify ts)

genTrie :: Trie' -> Q Exp
genTrie = go 0 where

  go :: Int -> Trie' -> Q Exp
  go !res (Branch' b d ts) | M.null ts =
    if res == 0 then
      (if b then [| eof |] else [| empty |])
    else
      error "impossible"

  go res (Path True d ws t) =
    let l = length ws in
    if res < l then
      let !res' = d - res in
      [| eof <!> (ensureBytes# res' >> $(scanBytes# False ws) >> $(go (d-l) t)) |]
    else
      [| eof <!> ($(scanBytes# False ws) >> $(go (res - l) t)) |]

  go res (Path False d ws t) =
    let l = length ws in
    if res < l then
      let !res' = d - res in
      [| ensureBytes# res' >> $(scanBytes# False ws) >> $(go (d-l) t) |]
    else
      [| $(scanBytes# False ws) >> $(go (res - l) t) |]

  go res (Branch' True d ts) =
    if res < 1 then
      [| eof <!> (ensureBytes# d >> $(branch d ts)) |]
    else
      [| eof <!> $(branch res ts) |]

  go res (Branch' False d ts) =
    if res < 1 then
      [| ensureBytes# d >> $(branch d ts) |]
    else
      branch res ts

  branch :: Int -> Map Word8 Trie' -> Q Exp
  branch res ts = do
    next <- (traverse . traverse) (go (res - 1)) (M.toList ts)
    pure $
      DoE [
        BindS (VarP (mkName "c")) (VarE 'scanAny8#),
        NoBindS (CaseE (VarE (mkName "c"))
           (map (\(w, t) ->
                   Match (LitP (IntegerL (fromIntegral w)))
                         (NormalB t)
                         [])
                next
            ++ [Match WildP (NormalB (VarE 'empty)) []]))
        ]

wordSet :: [String] -> Q Exp
wordSet = genTrie . pathify . mindepths . FlatParseIndent.fromList

--------------------------------------------------------------------------------

-- -- match :: Q Exp -> Q Exp
-- -- match _ = [| () |]
