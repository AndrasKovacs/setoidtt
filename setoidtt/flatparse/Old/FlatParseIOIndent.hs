

module Old.FlatParseIOIndent where

import qualified Control.Exception
import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as B
import Data.Bits
import Data.Char (ord)
import Data.Foldable
import Data.Word
import GHC.Exts
import GHC.Types
import GHC.Word
import GHC.Stack
import Language.Haskell.TH
import System.IO.Unsafe

--------------------------------------------------------------------------------

data Exception e =
    forall err. Control.Exception.Exception err => SomeException err
  | ExUser e

--------------------------------------------------------------------------------

type Res# s a = (# (# a, Addr#, Int#, State# s #) | State# s #)

pattern OK# :: a -> Addr# -> Int# -> State# s -> Res# s a
pattern OK# a s n rw = (# (# a, s, n, rw #) | #)

pattern Fail# :: State# s -> Res# s a
pattern Fail# w = (# | w #)
{-# complete OK#, Fail# #-}

type role Parser representational representational representational
newtype Parser r e a =
  Parser {runParser# :: forall s. r -> Addr# -> Addr# -> Int# -> State# s -> Res# s a}

instance Functor (Parser r e) where
  fmap f (Parser g) = Parser \r eob s n w -> case g r eob s n w of
    OK# a s n w -> let !b = f a in OK# b s n w
    Fail# w     -> Fail# w
  {-# inline fmap #-}
  (<$) a' (Parser g) = Parser \r eob s n w -> case g r eob s n w of
    OK# a s n w -> OK# a' s n w
    Fail# w     -> Fail# w
  {-# inline (<$) #-}

err :: e -> Parser r e a
err e = Parser \r eob s n w -> raise# (ExUser e)
{-# inline err #-}

empty :: Parser r e a
empty = Parser \r eob s n w -> Fail# w
{-# inline empty #-}

instance Applicative (Parser r e) where
  pure a = Parser \r eob s n w -> OK# a s n w
  {-# inline pure #-}
  Parser ff <*> Parser fa = Parser \r eob s n w -> case ff r eob s n w of
    OK# f s n w -> case fa r eob s n w of
      OK# a s n w -> let !b = f a in OK# b s n w
      Fail# w     -> Fail# w
    Fail# w     -> Fail# w
  {-# inline (<*>) #-}
  Parser fa <* Parser fb = Parser \r eob s n w -> case fa r eob s n w of
    OK# a s n w -> case fb r eob s n w of
      OK# b s n w -> OK# a s n w
      Fail# w   -> Fail# w
    Fail# w   -> Fail# w
  {-# inline (<*) #-}
  Parser fa *> Parser fb = Parser \r eob s n w -> case fa r eob s n w of
    OK# a s n w -> fb r eob s n w
    Fail# w     -> Fail# w
  {-# inline (*>) #-}

instance Monad (Parser r e) where
  return = pure
  {-# inline return #-}
  Parser fa >>= f = Parser \r eob s n w -> case fa r eob s n w of
    OK# a s n w -> runParser# (f a) r eob s n w
    Fail# w     -> Fail# w
  {-# inline (>>=) #-}
  Parser fa >> Parser fb = Parser \r eob s n w -> case fa r eob s n w of
    OK# a s n w -> fb r eob s n w
    Fail# w     -> Fail# w
  {-# inline (>>) #-}

derefChar8# :: Addr# -> Char#
derefChar8# addr = indexCharOffAddr# addr 0#
{-# inline derefChar8# #-}

eof :: Parser r e ()
eof = Parser \r eob s n w -> case eqAddr# eob s of
  1# -> OK# () s n w
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
(<|>) :: Parser r e a -> Parser r e a -> Parser r e a
(<|>) (Parser f) (Parser g) = Parser \r eob s n w ->
  case f r eob s n w of
    Fail# w -> g r eob s n w
    x       -> x
{-# inline (<|>) #-}

data CatchResult r a
  = CROK a Addr# Int#
  | CRFail

-- | Convert a parsing error into failure. Note: this has significant overhead.
--   For good performance, use lookahead parsers instead of `try`.
try :: Parser r e a -> Parser r e a
try (Parser f) = Parser \r eob s n w ->   -- rather crappy that we can only throw in LiftedRep
  case catch#
    (\w -> case f r eob s n w of
             OK# a s n w -> (# w, CROK a s n #)
             Fail# w     -> (# w, CRFail #))
    (\e w -> case e of
        ExUser e -> (# w, CRFail #)
        e        -> raiseIO# e w)
    (unsafeCoerce# w) of
      (# w, a #) -> case a of
        CROK a s n -> OK# a s n (unsafeCoerce# w)
        CRFail     -> Fail# (unsafeCoerce# w)
{-# inline try #-}

-- | Parse any `Char` in the ASCII range.
anyCharA :: Parser r e Char
anyCharA = Parser \r eob s n w -> case eqAddr# eob s of
  1# -> Fail# w
  _  -> case readCharOffAddr# s 0# w of
    (# w, c1 #) -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# s 1#) n w
      _  -> Fail# w
{-# inline anyCharA #-}

-- | Skip any `Char` in the ASCII range.
anyCharA_ :: Parser r e ()
anyCharA_ = () <$ anyCharA
{-# inline anyCharA_ #-}

-- | Parse any `Char`. This parser fails if the input is empty or no valid UTF-8
-- code point can be read from the input.
anyChar :: Parser r e Char
anyChar = Parser \r eob buf n w -> case eqAddr# eob buf of
  1# -> Fail# w
  _  -> case readCharOffAddr# buf 0# w of
    (# w, c1 #) -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# buf 1#) n w
      _  -> case eqAddr# eob (plusAddr# buf 1#) of
        1# -> Fail# w
        _ -> case readCharOffAddr# buf 1# w of
          (# w, c2 #) -> case c1 `leChar#` '\xDF'# of
            1# ->
              let resc = ((ord# c1 -# 0xC0#) `uncheckedIShiftL#` 6#) `orI#`
                          (ord# c2 -# 0x80#)
              in OK# (C# (chr# resc)) (plusAddr# buf 2#) n w
            _ -> case eqAddr# eob (plusAddr# buf 2#) of
              1# -> Fail# w
              _  -> case readCharOffAddr# buf 2# w of
                (# w, c3 #) -> case c1 `leChar#` '\xEF'# of
                  1# ->
                    let resc = ((ord# c1 -# 0xE0#) `uncheckedIShiftL#` 12#) `orI#`
                               ((ord# c2 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                                (ord# c3 -# 0x80#)
                    in OK# (C# (chr# resc)) (plusAddr# buf 3#) n w
                  _ -> case eqAddr# eob (plusAddr# buf 3#) of
                    1# -> Fail# w
                    _  -> case readCharOffAddr# buf 3# w of
                      (# w, c4 #) ->
                        let resc = ((ord# c1 -# 0xF0#) `uncheckedIShiftL#` 18#) `orI#`
                                   ((ord# c2 -# 0x80#) `uncheckedIShiftL#` 12#) `orI#`
                                   ((ord# c3 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                                    (ord# c4 -# 0x80#)
                        in OK# (C# (chr# resc)) (plusAddr# buf 4#) n w
{-# inline anyChar #-}

-- | Skip any `Char`.
anyChar_ :: Parser r e ()
anyChar_ = Parser \r eob buf n w -> case eqAddr# eob buf of
  1# -> Fail# w
  _  -> case readCharOffAddr# buf 0# w of
    (# w, c1 #) -> case c1 `leChar#` '\x7F'# of
      1# -> OK# () (plusAddr# buf 1#) n w
      _  ->
        let buf' =
              case c1 `leChar#` '\xDF'# of
                1# -> plusAddr# buf 2#
                _  -> case c1 `leChar#` '\xEF'# of
                    1# -> plusAddr# buf 3#
                    _ ->  plusAddr# buf 4#
        in case leAddr# buf' eob of
             1# -> OK# () buf' n w
             _  -> Fail# w
{-# inline anyChar_ #-}

-- | Parse a `Char` for which a predicate holds.
satisfy :: (Char -> Bool) -> Parser r e Char
satisfy f = Parser \r eob s n w -> case runParser# anyChar r eob s n w of
  OK# c s n w | f c -> OK# c s n w
  _                 -> Fail# w
{-#  inline satisfy #-}

-- | Parse an ASCII `Char` for which a predicate holds.
satisfyA :: (Char -> Bool) -> Parser r e Char
satisfyA f = Parser \r eob s n w -> case runParser# anyCharA r eob s n w of
  OK# c s n w | f c -> OK# c s n w
  _                 -> Fail# w
{-#  inline satisfyA #-}

-- | Skip a parser zero or more times. This fails if the given parser fails with
--   having consumed input.
many_ :: Parser r e a -> Parser r e ()
many_ (Parser f) = go where
  go = Parser \r eob s n w -> case f r eob s n w of
    OK# a s n w -> runParser# go r eob s n w
    Fail# w     -> OK# () s n w
{-# inline many_ #-}

-- | Branch on a parser: if the first argument suceeds, perform the second parser,
--   else the third.
br :: Parser r e a -> Parser r e b -> Parser r e b -> Parser r e b
br pa pt pf = Parser \r eob s n w -> case runParser# pa r eob s n w of
  OK# _ s n w -> runParser# pt r eob s n w
  Fail#   w   -> runParser# pf r eob s n w
{-# inline br #-}

-- | Skip a parser one or more times. This fails if the given parser fails with
--   having consumed input.
some_ :: Parser e e a -> Parser e e ()
some_ pa = pa >> many_ pa
{-# inline some_ #-}

chainl :: (b -> a -> b) -> Parser r e b -> Parser r e a -> Parser r e b
chainl f start elem = start >>= go where
  go b = do {!a <- elem; go $! f b a} <|> pure b
{-# inline chainl #-}

chainr :: (a -> b -> b) -> Parser r e a -> Parser r e b -> Parser r e b
chainr f elem end = go where
  go = (f <$> elem <*> go) <|> end
{-# inline chainr #-}

data Pos = Pos Addr#

instance Eq Pos where
  Pos p == Pos p' = isTrue# (eqAddr# p p')
  {-# inline (==) #-}

data Span = Span !Pos !Pos
  deriving Eq

getPos :: Parser r e Pos
getPos = Parser \r eob s n w -> OK# (Pos s) s n w
{-# inline getPos #-}

setPos :: Pos -> Parser r e ()
setPos (Pos s) = Parser \r eob s n w -> OK# () s n w
{-# inline setPos #-}

data Result e a =
    OK a Int B.ByteString
  | Fail
  | Err e
  deriving Show

catchIO :: forall a e. IO a -> (Exception e -> IO a) -> IO a
catchIO (IO io) f = IO (catch# io (\e -> case f e of IO f -> f))
{-# inline catchIO #-}

-- | Don't let any non-standard `Ex` exception escape. This should be used on
--   the top of the main function of the program.
fence :: HasCallStack => IO a -> IO a
fence act = act `catchIO` \case
  SomeException e -> Control.Exception.throw e
  _               -> error "impossible"
{-# inline fence #-}

runParser :: Parser r e a -> r -> Int -> B.ByteString -> Result e a
runParser (Parser f) r (I# n) b =
  unsafeDupablePerformIO $ fence do
    B.unsafeUseAsCString b \(Ptr buf) -> do
      let !(I# len) = B.length b
      let end = plusAddr# buf len
      runRW# \w -> case f r end buf n w of
        OK# a s n w  -> do
          let offset = minusAddr# s buf
          pure (OK a (I# n) (B.drop (I# offset) b))
        Fail# w ->
          pure Fail
{-# noinline runParser #-}

testParser :: Parser r e a -> r -> Int -> String -> Result e a
testParser pa r n s = runParser pa r n (B.pack (concatMap charToBytes s))


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

scanAny8# :: Parser r e Word8
scanAny8# = Parser \r eob s n w -> case readWord8OffAddr# s 0# w of
  (# w, c #) -> OK# (W8# c) (plusAddr# s 1#) n w
{-# inline scanAny8# #-}

scan8# :: Word -> Parser r e ()
scan8# (W# c) = Parser \r eob s n w ->
  case readWord8OffAddr# s 0# w of
    (# w, c' #) -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 1#) n w
      _  -> Fail# w
{-# inline scan8# #-}

scan16# :: Word -> Parser r e ()
scan16# (W# c) = Parser \r eob s n w ->
  case readWord16OffAddr# s 0# w of
    (# w, c' #) -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 2#) n w
      _  -> Fail# w
{-# inline scan16# #-}

scan32# :: Word -> Parser r e ()
scan32# (W# c) = Parser \r eob s n w ->
  case indexWord32OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 4#) n w
      _  -> Fail# w
{-# inline scan32# #-}

scan64# :: Word -> Parser r e ()
scan64# (W# c) = Parser \r eob s n w ->
  case readWord64OffAddr# s 0# w of
    (# w, c' #) -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 8#) n w
      _  -> Fail# w
{-# inline scan64# #-}

scanPartial64# :: Int -> Word -> Parser r e ()
scanPartial64# (I# len) (W# word) = Parser \r eob s n w ->
  case readWordOffAddr# s 0# w of
    (# st, word' #) -> case uncheckedIShiftL# (8# -# len) 3# of
      sh -> case uncheckedShiftL# word' sh of
        word' -> case uncheckedShiftRL# word' sh of
          word' -> case eqWord# word word' of
            1# -> OK# () (plusAddr# s len) n w
            _  -> Fail# st
{-# inline scanPartial64# #-}

ensureBytes# :: Int -> Parser r e ()
ensureBytes# (I# len) = Parser \r eob s n w ->
  case len  <=# minusAddr# eob s of
    1# -> OK# () s n w
    _  -> Fail# w
{-# inline ensureBytes# #-}

setBack# :: Int -> Parser r e ()
setBack# (I# i) = Parser \r eob s n w ->
  OK# () (plusAddr# s (negateInt# i)) n w
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
