
module Old.FlatParseIO where

import qualified Data.ByteString as B
-- import qualified Data.ByteString.Short.Internal as SB
import qualified Data.ByteString.Unsafe as B
-- import qualified Data.Text.Short as T
-- import qualified Data.Text.Short.Unsafe as T
-- import qualified Data.Map.Strict as M
-- import Data.Map (Map)
import Data.Bits
import Data.Char (ord)
import Data.Foldable
import Data.Word
import GHC.Exts
import GHC.Word
import Language.Haskell.TH
import System.IO.Unsafe


--------------------------------------------------------------------------------

type Res# s a = (# (# a, Addr#, State# s #) | (# State# s #) #)

pattern OK# :: a -> Addr# -> State# s -> Res# s a
pattern OK# a s rw = (# (# a, s, rw #) | #)

pattern Fail# :: State# s -> Res# s a
pattern Fail# rw = (# | (# rw #) #)
{-# complete OK#, Fail# #-}

type role Parser representational representational
newtype Parser e a =
  Parser {runParser# :: forall s. Addr# -> Addr# -> State# s -> Res# s a}

instance Functor (Parser e) where
  fmap f (Parser g) = Parser \r s w -> case g r s w of
    OK# a s w  -> let !b = f a in OK# b s w
    Fail# w    -> Fail# w
  {-# inline fmap #-}

  (<$) a' (Parser g) = Parser \r s w -> case g r s w of
    OK# a s w  -> OK# a' s w
    Fail# w    -> Fail# w
  {-# inline (<$) #-}

-- err :: e -> Parser e a
-- err e = Parser \r s -> Err# e
-- {-# inline err #-}

empty :: Parser e a
empty = Parser \r s w -> Fail# w
{-# inline empty #-}

instance Applicative (Parser e) where
  pure a = Parser \r s w -> OK# a s w
  {-# inline pure #-}
  Parser ff <*> Parser fa = Parser \r s w -> case ff r s w of
    OK# f s w -> case fa r s w of
      OK# a s w -> OK# (f a) s w
      Fail# w   -> Fail# w
    Fail# w -> Fail# w
  {-# inline (<*>) #-}
  Parser fa <* Parser fb = Parser \r s w -> case fa r s w of
    OK# a s w -> case fb r s w of
      OK# b s w -> OK# a s w
      Fail# w   -> Fail# w
    Fail# w   -> Fail# w
  {-# inline (<*) #-}
  Parser fa *> Parser fb = Parser \r s w -> case fa r s w of
    OK# a s w  -> fb r s w
    Fail# w    -> Fail# w
  {-# inline (*>) #-}

instance Monad (Parser e) where
  return = pure
  {-# inline return #-}
  Parser fa >>= f = Parser \r s w -> case fa r s w of
    OK# a s w -> runParser# (f a) r s w
    Fail# w   -> Fail# w
  {-# inline (>>=) #-}
  Parser fa >> Parser fb = Parser \r s w -> case fa r s w of
    OK# a s w -> fb r s w
    Fail# w   -> Fail# w
  {-# inline (>>) #-}

-- derefChar8# :: Addr# -> Char#
-- derefChar8# addr = indexCharOffAddr# addr 0#
-- {-# inline derefChar8# #-}

eof :: Parser e ()
eof = Parser \eob s w -> case eqAddr# eob s of
  1# -> OK# () s w
  _  -> Fail# w
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

-- | Choose between two parsers. If the first parser fails, we
--   try the second one, but if the first one throws an error,
--   we propagate the error.
infixr 6 <|>
(<|>) :: Parser e a -> Parser e a -> Parser e a
(<|>) (Parser f) (Parser g) = Parser \r s w ->
  case f r s w of
    Fail# w -> g r s w
    x       -> x
{-# inline (<|>) #-}

-- -- | Convert a parsing error into failure.
-- try :: Parser e a -> Parser e a
-- try (Parser f) = Parser \r s -> case f r s of
--   Err# _ -> Fail#
--   x      -> x
-- {-# inline try #-}

-- | Parse any `Char` in the ASCII range.
anyCharA :: Parser e Char
anyCharA = Parser \eob buf w -> case eqAddr# eob buf of
  1# -> Fail# w
  _  -> case readCharOffAddr# buf 0# w of
    (# w, c1 #) -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# buf 1#) w
      _  -> Fail# w
{-# inline anyCharA #-}

-- | Skip any `Char` in the ASCII range.
anyCharA_ :: Parser e ()
anyCharA_ = () <$ anyCharA
{-# inline anyCharA_ #-}

-- | Parse any `Char`. This parser fails if the input is empty or no valid UTF-8
-- code point can be read from the input.
anyChar :: Parser e Char
anyChar = Parser \eob buf w -> case eqAddr# eob buf of
  1# -> Fail# w
  _  -> case readCharOffAddr# buf 0# w of
    (# w, c1 #) -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# buf 1#) w
      _  -> case eqAddr# eob (plusAddr# buf 1#) of
        1# -> Fail# w
        _ -> case readCharOffAddr# buf 1# w of
          (# w, c2 #) -> case c1 `leChar#` '\xDF'# of
            1# ->
              let resc = ((ord# c1 -# 0xC0#) `uncheckedIShiftL#` 6#) `orI#`
                          (ord# c2 -# 0x80#)
              in OK# (C# (chr# resc)) (plusAddr# buf 2#) w
            _ -> case eqAddr# eob (plusAddr# buf 2#) of
              1# -> Fail# w
              _  -> case readCharOffAddr# buf 2# w of
                (# w, c3 #) -> case c1 `leChar#` '\xEF'# of
                  1# ->
                    let resc = ((ord# c1 -# 0xE0#) `uncheckedIShiftL#` 12#) `orI#`
                               ((ord# c2 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                                (ord# c3 -# 0x80#)
                    in OK# (C# (chr# resc)) (plusAddr# buf 3#) w
                  _ -> case eqAddr# eob (plusAddr# buf 3#) of
                    1# -> Fail# w
                    _  -> case readCharOffAddr# buf 3# w of
                      (# w, c4 #) ->
                        let resc = ((ord# c1 -# 0xF0#) `uncheckedIShiftL#` 18#) `orI#`
                                   ((ord# c2 -# 0x80#) `uncheckedIShiftL#` 12#) `orI#`
                                   ((ord# c3 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                                    (ord# c4 -# 0x80#)
                        in OK# (C# (chr# resc)) (plusAddr# buf 4#) w
{-# inline anyChar #-}

-- | Skip any `Char`.
anyChar_ :: Parser e ()
anyChar_ = Parser \eob buf w -> case eqAddr# eob buf of
  1# -> Fail# w
  _  -> case readCharOffAddr# buf 0# w of
    (# w, c1 #) -> case c1 `leChar#` '\x7F'# of
      1# -> OK# () (plusAddr# buf 1#) w
      _  ->
        let buf' =
              case c1 `leChar#` '\xDF'# of
                1# -> plusAddr# buf 2#
                _  -> case c1 `leChar#` '\xEF'# of
                    1# -> plusAddr# buf 3#
                    _ ->  plusAddr# buf 4#
        in case leAddr# buf' eob of
             1# -> OK# () buf' w
             _  -> Fail# w
{-# inline anyChar_ #-}

-- | Parse a `Char` for which a predicate holds.
satisfy :: (Char -> Bool) -> Parser e Char
satisfy f = Parser \r s w -> case runParser# anyChar r s w of
  OK# c s w | f c -> OK# c s w
  _               -> Fail# w
{-#  inline satisfy #-}

-- | Parse an ASCII `Char` for which a predicate holds.
satisfyA :: (Char -> Bool) -> Parser e Char
satisfyA f = Parser \r s w -> case runParser# anyCharA r s w of
  OK# c s w | f c -> OK# c s w
  _               -> Fail# w
{-#  inline satisfyA #-}

-- | Skip a parser zero or more times. This fails if the given parser fails with
--   having consumed input.
many_ :: Parser e a -> Parser e ()
many_ (Parser f) = go where
  go = Parser \r s w -> case f r s w of
    OK# a s w -> runParser# go r s w
    Fail# w   -> OK# () s w
{-# inline many_ #-}

br :: Parser e a -> Parser e b -> Parser e b -> Parser e b
br pa pt pf = Parser \r s w -> case runParser# pa r s w of
  OK# _ s w -> runParser# pt r s w
  Fail#   w -> runParser# pf r s w
{-# inline br #-}

manyBr_ :: Parser e a -> Parser e b -> Parser e ()
manyBr_ pa pb = go where
  go = br pa (pb >> go) (pure ())
{-# inline manyBr_ #-}

-- | Skip a parser one or more times. This fails if the given parser fails with
--   having consumed input.
some_ :: Parser e a -> Parser e ()
some_ pa = pa >> many_ pa
{-# inline some_ #-}

someBr_ :: Parser e a -> Parser e b -> Parser e ()
someBr_ pa pb = pa >> pb >> manyBr_ pa pb
{-# inline someBr_ #-}

chainl :: (b -> a -> b) -> Parser e b -> Parser e a -> Parser e b
chainl f start elem = start >>= go where
  go b = do {!a <- elem; go $! f b a} <|> pure b
{-# inline chainl #-}

chainr :: (a -> b -> b) -> Parser e a -> Parser e b -> Parser e b
chainr f elem end = go where
  go = (f <$> elem <*> go) <|> end
{-# inline chainr #-}

data Pos = Pos Addr#

instance Eq Pos where
  Pos p == Pos p' = isTrue# (eqAddr# p p')
  {-# inline (==) #-}

data Span = Span !Pos !Pos
  deriving Eq

getPos :: Parser e Pos
getPos = Parser \eob s -> OK# (Pos s) s
{-# inline getPos #-}

setPos :: Pos -> Parser e ()
setPos (Pos s) = Parser \r _ -> OK# () s
{-# inline setPos #-}

data Result e a =
    OK a B.ByteString
  | Fail
  | Err e
  deriving Show

runParser :: Parser e a -> B.ByteString -> Result e a
runParser (Parser f) b = unsafeDupablePerformIO do
  B.unsafeUseAsCString b \(Ptr buf) -> do
    let !(I# len) = B.length b
    let end = plusAddr# buf len
    runRW#  \w -> case f end buf w of
      OK# a s w  -> do
        let offset = minusAddr# s buf
        pure (OK a (B.drop (I# offset) b))
      Fail# w ->
        pure Fail
{-# noinline runParser #-}

testParser :: Parser e a -> String -> Result e a
testParser pa s = runParser pa (B.pack (concatMap charToBytes s))


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
scanAny8# = Parser \r s w -> case readWord8OffAddr# s 0# w of
  (# w, c #) -> OK# (W8# c) (plusAddr# s 1#) w
{-# inline scanAny8# #-}

scan8# :: Word -> Parser e ()
scan8# (W# c) = Parser \r s w ->
  case readWord8OffAddr# s 0# w of
    (# w, c' #) -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 1#) w
      _  -> Fail# w
{-# inline scan8# #-}

scan16# :: Word -> Parser e ()
scan16# (W# c) = Parser \r s w ->
  case readWord16OffAddr# s 0# w of
    (# w, c' #) -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 2#) w
      _  -> Fail# w
{-# inline scan16# #-}

scan32# :: Word -> Parser e ()
scan32# (W# c) = Parser \r s ->
  case indexWord32OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 4#)
      _  -> Fail#
{-# inline scan32# #-}

scan64# :: Word -> Parser e ()
scan64# (W# c) = Parser \r s w ->
  case readWord64OffAddr# s 0# w of
    (# w, c' #) -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 8#) w
      _  -> Fail# w
{-# inline scan64# #-}

scanPartial64# :: Int -> Word -> Parser e ()
scanPartial64# (I# len) (W# w) = Parser \r s st ->
  case readWordOffAddr# s 0# st of
    (# st, w' #) -> case uncheckedIShiftL# (8# -# len) 3# of
      sh -> case uncheckedShiftL# w' sh of
        w' -> case uncheckedShiftRL# w' sh of
          w' -> case eqWord# w w' of
            1# -> OK# () (plusAddr# s len) st
            _  -> Fail# st
{-# inline scanPartial64# #-}

ensureBytes# :: Int -> Parser e ()
ensureBytes# (I# len) = Parser \eob s ->
  case len  <=# minusAddr# eob s of
    1# -> OK# () s
    _  -> Fail#
{-# inline ensureBytes# #-}

setBack# :: Int -> Parser e ()
setBack# (I# i) = Parser \eob s ->
  OK# () (plusAddr# s (negateInt# i))
{-# inline setBack# #-}


scanBytes# :: [Word8] -> Q Exp
scanBytes# bytes = do
  let !(leading, w8s) = splitBytes bytes
      !scanw8s        = go w8s where
                         go (w8:[] ) = [| scan64# w8 |]
                         go (w8:w8s) = [| scan64# w8 >> $(go w8s) |]
                         go []       = [| pure () |]
  case w8s of
    [] -> go leading
          where
            go (a:b:c:d:[]) = let !w = packBytes [a, b, c, d] in [| scan32# w |]
            go (a:b:c:d:ws) = let !w = packBytes [a, b, c, d] in [| scan32# w >> $(go ws) |]
            go (a:b:[])     = let !w = packBytes [a, b]       in [| scan16# w |]
            go (a:b:ws)     = let !w = packBytes [a, b]       in [| scan16# w >> $(go ws) |]
            go (a:[])       = [| scan8# a |]
            go []           = [| pure () |]
    _  -> case leading of

      []              -> scanw8s
      [a]             -> [| scan8# a >> $scanw8s |]
      ws@[a, b]       -> let !w = packBytes ws in [| scan16# w >> $scanw8s |]
      ws@[a, b, c, d] -> let !w = packBytes ws in [| scan32# w >> $scanw8s |]
      ws              -> let !w = packBytes ws
                             !l = length ws
                         in [| scanPartial64# l w >> $scanw8s |]

string :: String -> Q Exp
string str = do
  let !bytes = strToBytes str
      !len   = length bytes
  [| ensureBytes# len >> $(scanBytes# bytes) |]

char :: Char -> Q Exp
char c = string [c]
