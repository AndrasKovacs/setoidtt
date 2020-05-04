
module FlatParse where

import qualified Data.ByteString as B
import qualified Data.ByteString.Short.Internal as SB
import qualified Data.ByteString.Unsafe as B
import qualified Data.Text.Short as T
import qualified Data.Text.Short.Unsafe as T

import Data.Bits
import Data.Char (ord)
import Data.Foldable
import Data.Word
import GHC.Exts
import Language.Haskell.TH
import System.IO.Unsafe

--------------------------------------------------------------------------------

data Error e = Default | Custom e
  deriving Show

type Read# r = (# Addr#, r #)
type Res# e a = (# (# a, Addr# #) | (# Error e, Addr# #) #)

pattern OK# :: a -> Addr# -> Res# e a
pattern OK# a s = (# (# a, s #) | #)

pattern Err# :: Error e -> Addr# -> Res# e a
pattern Err# e s = (# | (# e, s #) #)
{-# complete OK#, Err# #-}

newtype Parser r e a = Parser {runParser# :: Read# r -> Addr# -> Res# e a}

instance Functor (Parser r e) where
  fmap f (Parser g) = Parser \r s -> case g r s of
    OK# a s  -> let !b = f a in OK# b s
    Err# e s -> Err# e s
  {-# inline fmap #-}

  (<$) a' (Parser g) = Parser \r s -> case g r s of
    OK# a s  -> OK# a' s
    Err# e s -> Err# e s
  {-# inline (<$) #-}

err :: e -> Parser r e a
err e = Parser \r s -> Err# (Custom e) s
{-# inline err #-}

empty :: Parser r e a
empty = Parser \r s -> Err# Default s
{-# inline empty #-}

instance Applicative (Parser r e) where
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

instance Monad (Parser r e) where
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

ask :: Parser r e r
ask = Parser \(# _, r #) s -> OK# r s
{-# inline ask #-}

local :: (r -> r') -> Parser r' e a -> Parser r e a
local f (Parser fa) = Parser \(# eob, r #) s -> fa (# eob, f r #) s
{-# inline local #-}

derefChar# :: Addr# -> Char#
derefChar# addr = indexCharOffAddr# addr 0#
{-# inline derefChar# #-}

eof :: Parser r e ()
eof = Parser \(# eob, _ #) s -> case eqAddr# eob s of
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

infixr 6 <|>
(<|>) :: Parser r e a -> Parser r e a -> Parser r e a
(<|>) (Parser f) (Parser g) = Parser \r s ->
  case f r s of
    Err# e _ -> g r s
    x        -> x
{-# inline (<|>) #-}

infixr 6 <!>
(<!>) :: Parser r e a -> Parser r e a -> Parser r e a
(<!>) (Parser f) (Parser g) = Parser \r s ->
  case f r s of
    Err# e s' -> case eqAddr# s s' of
                   1# -> g r s
                   _  -> Err# e s'
    x         -> x
{-# inline (<!>) #-}

try :: Parser r e a -> Parser r e a
try (Parser f) = Parser \r s -> case f r s of
  Err# e _ -> Err# e s
  x        -> x
{-# inline try #-}

anyCharA :: Parser r e Char
anyCharA = Parser \(# eob, i #) buf -> case eqAddr# eob buf of
  1# -> Err# Default buf
  _  -> case derefChar# buf of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# buf 1#)
      _  -> Err# Default buf
{-# inline anyCharA #-}

anyCharA_ :: Parser r e ()
anyCharA_ = () <$ anyCharA
{-# inline anyCharA_ #-}

anyChar :: Parser r e Char
anyChar = Parser \(# eob, i #) buf -> case eqAddr# eob buf of
  1# -> Err# Default buf
  _  -> case derefChar# buf of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# buf 1#)
      _  -> case indexCharOffAddr# buf 1# of
        c2 -> case c1 `leChar#` '\xDF'# of
          1# ->
            let resc = ((ord# c1 -# 0xC0#) `uncheckedIShiftL#` 6#) `orI#`
                        (ord# c2 -# 0x80#)
            in OK# (C# (chr# resc)) (plusAddr# buf 2#)
          _ -> case indexCharOffAddr# buf 2# of
            c3 -> case c1 `leChar#` '\xEF'# of
              1# ->
                let resc = ((ord# c1 -# 0xE0#) `uncheckedIShiftL#` 12#) `orI#`
                           ((ord# c2 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                            (ord# c3 -# 0x80#)
                in OK# (C# (chr# resc)) (plusAddr# buf 3#)
              _ -> case indexCharOffAddr# buf 3# of
                c4 ->
                  let resc = ((ord# c1 -# 0xF0#) `uncheckedIShiftL#` 18#) `orI#`
                             ((ord# c2 -# 0x80#) `uncheckedIShiftL#` 12#) `orI#`
                             ((ord# c3 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                              (ord# c4 -# 0x80#)
                  in OK# (C# (chr# resc)) (plusAddr# buf 4#)
{-# inline anyChar #-}

anyChar_ :: Parser r e ()
anyChar_ = Parser \(# eob, i #) buf -> case eqAddr# eob buf of
  1# -> Err# Default buf
  _  -> case derefChar# buf of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# () (plusAddr# buf 1#)
      _  -> case c1 `leChar#` '\xDF'# of
          1# -> OK# () (plusAddr# buf 2#)
          _  -> case c1 `leChar#` '\xEF'# of
              1# -> OK# () (plusAddr# buf 3#)
              _ ->  OK# () (plusAddr# buf 4#)
{-# inline anyChar_ #-}

satisfy :: (Char -> Bool) -> Parser r e Char
satisfy f = Parser \r s -> case runParser# anyChar r s of
  OK# c s | f c -> OK# c s
  OK# c s       -> Err# Default s
  Err# e s      -> Err# e s
{-#  inline satisfy #-}

satisfyA :: (Char -> Bool) -> Parser r e Char
satisfyA f = Parser \r s -> case runParser# anyCharA r s of
  OK# c s | f c -> OK# c s
  OK# c s       -> Err# Default s
  Err# e s      -> Err# e s
{-#  inline satisfyA #-}

many_ :: Parser r e a -> Parser r e ()
many_ (Parser f) = go where
  go = Parser \r s -> case f r s of
    Err# e _  -> OK# () s
    OK# a s   -> runParser# go r s
{-# inline many_ #-}

some_ :: Parser r e a -> Parser r e ()
some_ pa = pa >> many_ pa
{-# inline some_ #-}

manyTill_ :: Parser r e a -> Parser r e b -> Parser r e ()
manyTill_ pa end = go where
  go = (() <$ end) <|> (pa >> go)
{-# inline manyTill_ #-}

chainl :: (b -> a -> b) -> Parser r e b -> Parser r e a -> Parser r e b
chainl f start elem = start >>= go where
  go b = do {a <- elem; go $! f b a} <|> pure b
{-# inline chainl #-}

chainr :: (a -> b -> b) -> Parser r e a -> Parser r e b -> Parser r e b
chainr f elem end = go where
  go = (f <$> elem <*> go) <|> end
{-# inline chainr #-}

silent :: Parser r e a -> Parser r e a
silent pa = Parser \r s -> case runParser# pa r s of
  Err# e s -> Err# Default s
  x        -> x
{-# inline silent #-}

data RawSpan = RawSpan Addr# Addr#

spanned :: Parser r e a -> Parser r e (a, RawSpan)
spanned (Parser f) = Parser \r s -> case f r s of
  Err# e s  -> Err# e s
  OK# a s'  -> OK# (a, RawSpan s s') s'
{-# inline spanned #-}

spanToShortText :: RawSpan -> T.ShortText
spanToShortText (RawSpan start end) =
  let len  = minusAddr# end start
  in T.fromShortByteStringUnsafe (SB.SBS (runRW# \s ->
       case newByteArray# len s of
         (# s, marr #) -> case copyAddrToByteArray# start marr 0# len s of
           s -> case unsafeFreezeByteArray# marr s of
             (# s, arr #) -> arr))
{-# inline spanToShortText #-}

asShortText :: Parser r e a -> Parser r e (T.ShortText)
asShortText p = fmap (\(_ ,s) -> spanToShortText s) (spanned p)
{-# inline asShortText #-}

newtype Pos = Pos Int
  deriving (Eq, Show) via Int

getPos :: Parser r e Pos
getPos = Parser \(# eob, _ #) s -> OK# (Pos (I# (minusAddr# eob s))) s
{-# inline getPos #-}

data Result e a = OK a B.ByteString | Err (Error e) B.ByteString
  deriving Show

runParser :: Parser r e a -> r -> B.ByteString -> Result e a
runParser (Parser f) r b = unsafeDupablePerformIO do
  B.unsafeUseAsCString b \(Ptr buf) -> do
    let !(I# len) = B.length b
    let end = plusAddr# buf len
    case f (# end, r #) buf of
      Err# e s  -> do
        let offset = minusAddr# s buf
        pure (Err e (B.drop (I# offset) b))
      OK# a s   -> do
        let offset = minusAddr# s buf
        pure (OK a (B.drop (I# offset) b))

runParser' :: Parser r e a -> r -> String -> Result e a
runParser' p r str = runParser p r (B.pack (charToBytes =<< str))

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

scan8# :: Word -> Parser r e ()
scan8# (W# c) = Parser \r s ->
  case indexWord8OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 1#)
      _  -> Err# Default s
{-# inline scan8# #-}

scan16# :: Word -> Parser r e ()
scan16# (W# c) = Parser \r s ->
  case indexWord16OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 2#)
      _  -> Err# Default s
{-# inline scan16# #-}

scan32# :: Word -> Parser r e ()
scan32# (W# c) = Parser \r s ->
  case indexWord32OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 4#)
      _  -> Err# Default s
{-# inline scan32# #-}

scan64# :: Word -> Parser r e ()
scan64# (W# c) = Parser \r s ->
  case indexWord64OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 8#)
      _  -> Err# Default s
{-# inline scan64# #-}

scanPartial64# :: Int -> Word -> Parser r e ()
scanPartial64# (I# len) (W# w) = Parser \r s ->
  case indexWordOffAddr# s 0# of
    w' -> case uncheckedIShiftL# (8# -# len) 3# of
      sh -> case uncheckedShiftL# w' sh of
        w' -> case uncheckedShiftRL# w' sh of
          w' -> case eqWord# w w' of
            1# -> OK# () (plusAddr# s len)
            _  -> Err# Default s
{-# inline scanPartial64# #-}

ensureBytes# :: Int -> Parser r e ()
ensureBytes# (I# len) = Parser \(# eob, _ #) s ->
  case len <=# minusAddr# eob s of
    1# -> OK# () s
    _  -> Err# Default s
{-# inline ensureBytes# #-}

string :: String -> Q Exp
string str = do
  let bytes          = strToBytes str
      len            = length bytes
      (leading, w8s) = splitBytes (strToBytes str)
      scanw8s        = go w8s where
                         go (w8:[] ) = [| scan64# w8 |]
                         go (w8:w8s) = [| scan64# w8 >> $(go w8s) |]
                         go []       = [| pure () |]
  case w8s of
    [] -> [| ensureBytes# len >> $(go leading) |] where
             go (a:b:c:d:[]) = let w = packBytes [a, b, c, d] in [| scan32# w |]
             go (a:b:c:d:ws) = let w = packBytes [a, b, c, d] in [| scan32# w >> $(go ws) |]
             go (a:b:[])     = let w = packBytes [a, b]       in [| scan16# w |]
             go (a:b:ws)     = let w = packBytes [a, b]       in [| scan16# w >> $(go ws) |]
             go (a:[])       = [| scan8# a |]
             go []           = [| pure () |]
    _  -> case leading of
      []  -> [| ensureBytes# len >> $scanw8s |]
      [a] -> [| ensureBytes# len >> scan8# a >> $scanw8s |]
      ws  -> let w = packBytes ws
                 l = length ws
             in [| ensureBytes# len >> scanPartial64# l w >> $scanw8s |]

char :: Char -> Q Exp
char c = string [c]
