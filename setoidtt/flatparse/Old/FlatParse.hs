
module Old.FlatParse where

import qualified Data.ByteString as B
import qualified Data.ByteString.Short.Internal as SB
import qualified Data.ByteString.Unsafe as B
import qualified Data.Text.Short as T
import qualified Data.Text.Short.Unsafe as T
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

data Error e = Default | Custom e
  deriving Show

type Res# e a = (# (# a, Addr# #) | (# Error e, Addr# #) #)

pattern OK# :: a -> Addr# -> Res# e a
pattern OK# a s = (# (# a, s #) | #)

pattern Err# :: Error e -> Addr# -> Res# e a
pattern Err# e s = (# | (# e, s #) #)
{-# complete OK#, Err# #-}

newtype Parser e a = Parser {runParser# :: Addr# -> Addr# -> Res# e a}

instance Functor (Parser e) where
  fmap f (Parser g) = Parser \r s -> case g r s of
    OK# a s  -> let !b = f a in OK# b s
    Err# e s -> Err# e s
  {-# inline fmap #-}

  (<$) a' (Parser g) = Parser \r s -> case g r s of
    OK# a s  -> OK# a' s
    Err# e s -> Err# e s
  {-# inline (<$) #-}

err :: e -> Parser e a
err e = Parser \r s -> Err# (Custom e) s
{-# inline err #-}

empty :: Parser e a
empty = Parser \r s -> Err# Default s
{-# inline empty #-}

instance Applicative (Parser e) where
  pure a = Parser \r s -> OK# a s
  {-# inline pure #-}
  Parser ff <*> Parser fa = Parser \r s -> case ff r s of
    Err# e s -> Err# e s
    OK# f s -> case fa r s of
      Err# e s -> Err# e s
      OK# a s  -> OK# (f a) s
  {-# inline (<*>) #-}
  Parser fa <* Parser fb = Parser \r s -> case fa r s of
    Err# e s -> Err# e s
    OK# a s -> case fb r s of
      Err# e s -> Err# e s
      OK# b s -> OK# a s
  {-# inline (<*) #-}
  Parser fa *> Parser fb = Parser \r s -> case fa r s of
    Err# e s -> Err# e s
    OK# a s  -> fb r s
  {-# inline (*>) #-}

instance Monad (Parser e) where
  return = pure
  {-# inline return #-}
  Parser fa >>= f = Parser \r s -> case fa r s of
    Err# e s -> Err# e s
    OK# a s  -> runParser# (f a) r s
  {-# inline (>>=) #-}
  Parser fa >> Parser fb = Parser \r s -> case fa r s of
    Err# e s -> Err# e s
    OK# a s  -> fb r s
  {-# inline (>>) #-}

derefChar8# :: Addr# -> Char#
derefChar8# addr = indexCharOffAddr# addr 0#
{-# inline derefChar8# #-}

eof :: Parser e ()
eof = Parser \eob s -> case eqAddr# eob s of
  1# -> OK# () s
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
(<!>) (Parser f) (Parser g) = Parser \r s ->
  case f r s of
    Err# e _ -> g r s
    x        -> x
{-# inline (<!>) #-}

-- | Choose between two parsers. The second parser is only tried
--   if the first one fails without having consumed input.
infixr 6 <|>
(<|>) :: Parser e a -> Parser e a -> Parser e a
(<|>) (Parser f) (Parser g) = Parser \r s ->
  case f r s of
    Err# e s' -> case eqAddr# s s' of
                   1# -> g r s
                   _  -> Err# e s'
    x         -> x
{-# inline (<|>) #-}

-- | Reset the input position if the given parser fails.
try :: Parser e a -> Parser e a
try (Parser f) = Parser \r s -> case f r s of
  Err# e _ -> Err# e s
  x        -> x
{-# inline try #-}

-- | Parse any `Char` in the ASCII range.
anyCharA :: Parser e Char
anyCharA = Parser \eob buf -> case eqAddr# eob buf of
  1# -> Err# Default buf
  _  -> case derefChar8# buf of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# buf 1#)
      _  -> Err# Default buf
{-# inline anyCharA #-}

-- | Skip any `Char` in the ASCII range.
anyCharA_ :: Parser e ()
anyCharA_ = () <$ anyCharA
{-# inline anyCharA_ #-}

-- | Get byte length of code point from the first byte.
getUTF8Len# :: Word# -> Int#
getUTF8Len# w = word2Int# (clz8# (not# w))
{-# inline getUTF8Len# #-}

-- | Parse any `Char`. This parser fails if the input is empty or no valid UTF-8
-- code point can be read from the input.
anyChar :: Parser e Char
anyChar = Parser \eob buf -> case eqAddr# eob buf of
  1# -> Err# Default buf
  _  -> case derefChar8# buf of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# buf 1#)
      _  -> case eqAddr# eob (plusAddr# buf 1#) of
        1# -> Err# Default buf
        _ -> case indexCharOffAddr# buf 1# of
          c2 -> case c1 `leChar#` '\xDF'# of
            1# ->
              let resc = ((ord# c1 -# 0xC0#) `uncheckedIShiftL#` 6#) `orI#`
                          (ord# c2 -# 0x80#)
              in OK# (C# (chr# resc)) (plusAddr# buf 2#)
            _ -> case eqAddr# eob (plusAddr# buf 2#) of
              1# -> Err# Default buf
              _  -> case indexCharOffAddr# buf 2# of
                c3 -> case c1 `leChar#` '\xEF'# of
                  1# ->
                    let resc = ((ord# c1 -# 0xE0#) `uncheckedIShiftL#` 12#) `orI#`
                               ((ord# c2 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                                (ord# c3 -# 0x80#)
                    in OK# (C# (chr# resc)) (plusAddr# buf 3#)
                  _ -> case eqAddr# eob (plusAddr# buf 3#) of
                    1# -> Err# Default buf
                    _  -> case indexCharOffAddr# buf 3# of
                      c4 ->
                        let resc = ((ord# c1 -# 0xF0#) `uncheckedIShiftL#` 18#) `orI#`
                                   ((ord# c2 -# 0x80#) `uncheckedIShiftL#` 12#) `orI#`
                                   ((ord# c3 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                                    (ord# c4 -# 0x80#)
                        in OK# (C# (chr# resc)) (plusAddr# buf 4#)
{-# inline anyChar #-}

-- | Skip any `Char`.
anyChar_ :: Parser e ()
anyChar_ = Parser \eob buf -> case eqAddr# eob buf of
  1# -> Err# Default buf
  _  -> case derefChar8# buf of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# () (plusAddr# buf 1#)
      _  ->
        let buf' =
              case c1 `leChar#` '\xDF'# of
                1# -> plusAddr# buf 2#
                _  -> case c1 `leChar#` '\xEF'# of
                    1# -> plusAddr# buf 3#
                    _ ->  plusAddr# buf 4#
        in case leAddr# buf' eob of
             1# -> OK# () buf'
             _  -> Err# Default buf
{-# inline anyChar_ #-}

-- | Parser a `Char` for which a predicate holds.
satisfy :: (Char -> Bool) -> Parser e Char
satisfy f = Parser \r s -> case runParser# anyChar r s of
  OK# c s | f c -> OK# c s
  OK# c _       -> Err# Default s
  Err# e s      -> Err# e s
{-#  inline satisfy #-}

-- | Parse an ASCII `Char` for which a predicate holds.
satisfyA :: (Char -> Bool) -> Parser e Char
satisfyA f = Parser \r s -> case runParser# anyCharA r s of
  OK# c s | f c -> OK# c s
  OK# c _       -> Err# Default s
  Err# e s      -> Err# e s
{-#  inline satisfyA #-}

-- | Skip a parser zero or more times. This fails if the given parser fails with
--   having consumed input.
many_ :: Parser e a -> Parser e ()
many_ (Parser f) = go where
  go = Parser \r s -> case f r s of
    Err# e s' -> case eqAddr# s s' of
                   1# -> OK# () s
                   _  -> Err# e s'
    OK# a s   -> runParser# go r s
{-# inline many_ #-}

manyBr_ :: Parser e a -> Parser e b -> Parser e ()
manyBr_ pa pb = go where
  go = br pa (pb >> go) (pure ())
{-# inline manyBr_ #-}

manyTok_ :: Parser e a -> Parser e ()
manyTok_ (Parser f) = go where
  go = Parser \r s -> case f r s of
    Err# _ _ -> OK# () s
    OK# a s  -> runParser# go r s
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
silent pa = Parser \r s -> case runParser# pa r s of
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
spanned (Parser f) = Parser \r s -> case f r s of
  Err# e s  -> Err# e s
  OK# a s'  -> OK# (a, Span (Pos s) (Pos s')) s'
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
getPos = Parser \eob s -> OK# (Pos s) s
{-# inline getPos #-}

setPos :: Pos -> Parser e ()
setPos (Pos s) = Parser \r _ -> OK# () s
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
--   of the input buffer. Restore the original state after the parser finishes.
inSpan :: Span -> Parser e a -> Parser e a
inSpan (Span (Pos start) (Pos end)) (Parser f) =
  Parser \oldend oldstart -> case f end start of
    OK# a _  -> OK# a oldstart
    Err# e _ -> Err# e oldstart
{-# inline inSpan #-}

data Result e a = OK a B.ByteString | Err (Error e) B.ByteString
  deriving Show

runParser :: Parser e a -> B.ByteString -> Result e a
runParser (Parser f) b = unsafeDupablePerformIO do
  B.unsafeUseAsCString b \(Ptr buf) -> do
    let !(I# len) = B.length b
    let end = plusAddr# buf len
    case f end buf of
      Err# e s  -> do
        let offset = minusAddr# s buf
        pure (Err e (B.drop (I# offset) b))
      OK# a s   -> do
        let offset = minusAddr# s buf
        pure (OK a (B.drop (I# offset) b))

testParser :: Parser e a -> String -> Result e a
testParser pa s = runParser pa (B.pack (concatMap charToBytes s))

br :: Parser e a -> Parser e b -> Parser e b -> Parser e b
br pa pt pf = Parser \r s -> case runParser# pa r s of
  OK# _ s  -> runParser# pt r s
  Err# _ _ -> runParser# pf r s
{-# inline br #-}

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
scanAny8# = Parser \r s -> OK# (W8# (indexWord8OffAddr# s 0#)) (plusAddr# s 1#)
{-# inline scanAny8# #-}

scan8# :: Word -> Parser e ()
scan8# (W# c) = Parser \r s ->
  case indexWord8OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 1#)
      _  -> Err# Default s
{-# inline scan8# #-}

scan16# :: Word -> Parser e ()
scan16# (W# c) = Parser \r s ->
  case indexWord16OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 2#)
      _  -> Err# Default s
{-# inline scan16# #-}

scan32# :: Word -> Parser e ()
scan32# (W# c) = Parser \r s ->
  case indexWord32OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 4#)
      _  -> Err# Default s
{-# inline scan32# #-}

scan64# :: Word -> Parser e ()
scan64# (W# c) = Parser \r s ->
  case indexWord64OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 8#)
      _  -> Err# Default s
{-# inline scan64# #-}

scanPartial64# :: Int -> Word -> Parser e ()
scanPartial64# (I# len) (W# w) = Parser \r s ->
  case indexWordOffAddr# s 0# of
    w' -> case uncheckedIShiftL# (8# -# len) 3# of
      sh -> case uncheckedShiftL# w' sh of
        w' -> case uncheckedShiftRL# w' sh of
          w' -> case eqWord# w w' of
            1# -> OK# () (plusAddr# s len)
            _  -> Err# Default s
{-# inline scanPartial64# #-}

ensureBytes# :: Int -> Parser e ()
ensureBytes# (I# len) = Parser \eob s ->
  case len  <=# minusAddr# eob s of
    1# -> OK# () s
    _  -> Err# Default s
{-# inline ensureBytes# #-}

setBack# :: Int -> Parser e ()
setBack# (I# i) = Parser \eob s ->
  OK# () (plusAddr# s (negateInt# i))
{-# inline setBack# #-}

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
      ws  -> let !w = packBytes ws
                 !l = length ws
                 !op = case l of
                   1 -> [| scan8#  w |]
                   2 -> [| scan16# w |]
                   4 -> [| scan32# w |]
                   _ -> [| scanPartial64# l w |]
             in if isToken then [| try ($op >> $scanw8s) |]
                           else [| $op >> $scanw8s |]

string :: String -> Q Exp
string str = do
  let !bytes = strToBytes str
      !len   = length bytes
  [| ensureBytes# len >> $(scanBytes# True bytes) |]

char :: Char -> Q Exp
char c = string [c]
