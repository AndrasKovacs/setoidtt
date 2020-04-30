
module Parsers where

import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as B
import qualified Data.ByteString.Short.Internal as SB
import qualified Data.Text.Short as T
import qualified Data.Text.Short.Unsafe as T

import Data.Bits
import Data.Char (ord)
import Data.Word
import GHC.Exts
import GHC.Word
import System.IO.Unsafe

import Language.Haskell.TH

data Error e =
    Default
  | Custom e
  | Eof
  | NonEof
  | Latin1
  | Char !Char
  | String String
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
    OK# a s  -> let b = f a in OK# b s
    Err# e s -> Err# e s
  {-# inline fmap #-}

  (<$) a' (Parser g) = Parser \r s -> case g r s of
    OK# a s  -> OK# a' s
    Err# e s -> Err# e s
  {-# inline (<$) #-}

err :: Error e -> Parser r e a
err e = Parser \r s -> Err# e s
{-# inline err #-}

customErr :: e -> Parser r e a
customErr e = Parser \r s -> Err# (Custom e) s
{-# inline customErr #-}

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
  _  -> Err# Eof s
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

anyCharL1 :: Parser r e Char
anyCharL1 = Parser \(# eob, i #) buf -> case eqAddr# eob buf of
  1# -> Err# NonEof buf
  _  -> case derefChar# buf of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# buf 1#)
      _  -> Err# Latin1 buf
{-# inline anyCharL1 #-}

anyCharL1_ :: Parser r e ()
anyCharL1_ = () <$ anyCharL1
{-# inline anyCharL1_ #-}

anyChar :: Parser r e Char
anyChar = Parser \(# eob, i #) buf -> case eqAddr# eob buf of
  1# -> Err# NonEof buf
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
  1# -> Err# NonEof buf
  _  -> case derefChar# buf of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# () (plusAddr# buf 1#)
      _  -> case c1 `leChar#` '\xDF'# of
          1# -> OK# () (plusAddr# buf 2#)
          _  -> case c1 `leChar#` '\xEF'# of
              1# -> OK# () (plusAddr# buf 3#)
              _ ->  OK# () (plusAddr# buf 4#)
{-# inline anyChar_ #-}

satisfy :: Error e -> (Char -> Bool) -> Parser r e Char
satisfy e f = (do {c <- anyChar; if f c then pure c else err e}) <|> err e
{-#  inline satisfy #-}

satisfyL1 :: Error e -> (Char -> Bool) -> Parser r e Char
satisfyL1 e f = (do {c <- anyCharL1; if f c then pure c else err e}) <|> err e
{-#  inline satisfyL1 #-}

scanByte# :: String -> Word8 -> Parser r e ()
scanByte# str (W8# c) = Parser \r s ->
  case indexWord8OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 1#)
      _  -> Err# (String str) s
{-# inline scanByte# #-}

ensureBytes# :: Int -> Parser r e ()
ensureBytes# (I# len) = Parser \(# eob, _ #) s ->
  case len <=# (minusAddr# eob s) of
    1# -> OK# () s
    _  -> Err# NonEof s
{-# inline ensureBytes# #-}

string :: String -> Q Exp
string []  = error "scan: empty string"
string str = do
  let bytes = charToBytes =<< str
      !len  = length bytes
      go [w]    = [| scanByte# str w |]
      go (w:ws) = [| scanByte# str w >> $(go ws) |]
      go _      = undefined
  [| ensureBytes# len >> $(go bytes) |]

char :: Char -> Q Exp
char c = string [c]

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

chainl1 :: (b -> a -> b) -> Parser r e a -> Parser r e b -> Parser r e b
chainl1 f elem start = start >>= go where
  go b = do {a <- elem; go $! f b a} <|> pure b
{-# inline chainl1 #-}

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

newtype BackwardsPos = BackwardsPos Int
  deriving (Eq, Show, Ord, Num) via Int

flipPos :: B.ByteString -> BackwardsPos -> Int
flipPos b (BackwardsPos p)
  | p <= B.length b = B.length b - p
  | otherwise       = error "flipPos: out of bounds"
{-# inline flipPos #-}

-- | This is byte position counted backwards from the end of the input.
getPos :: Parser r e BackwardsPos
getPos = Parser \(# eob, _ #) s -> OK# (BackwardsPos (I# (minusAddr# eob s))) s
{-# inline getPos #-}

data Res e a = OK a B.ByteString | Err (Error e) B.ByteString
  deriving Show

runParser :: Parser r e a -> r -> B.ByteString -> Res e a
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

runParser' :: Parser r e a -> r -> String -> Res e a
runParser' p r str = runParser p r (B.pack (charToBytes =<< str))
