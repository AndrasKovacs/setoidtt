
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
import GHC.Word
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

defaultErr :: Parser r e a
defaultErr = Parser \r s -> Err# Default s
{-# inline defaultErr #-}

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
satisfy f = (do {c <- anyChar; if f c then pure c else err Default}) <|> err Default
{-#  inline satisfy #-}

satisfyA :: (Char -> Bool) -> Parser r e Char
satisfyA f = (do {c <- anyCharA; if f c then pure c else defaultErr})
          <|> defaultErr
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

runParser' :: Parser r e a -> r -> String -> Res e a
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

trySplit :: Int -> [a] -> Maybe ([a], [a])
trySplit n as | n <= 0 = Just ([], as)
trySplit n []     = Nothing
trySplit n (a:as) = (\(as1, as2) -> (a:as1, as2)) <$> trySplit (n - 1) as

packBytes :: [Word8] -> Word
packBytes = fst . foldl' go (0, 0) where
  go (acc, shift) w | shift == 64 = error "packWords: too many bytes"
  go (acc, shift) w = (unsafeShiftL (fromIntegral w) shift .|. acc, shift+8)

vectorize :: [Word8] -> ([Word], Maybe (Either (Int, Word) Word8))
vectorize ws = case trySplit 8 ws of
  Just (w8, rest) -> let (w8s, end) = vectorize rest
                     in (packBytes w8:w8s, end)
  Nothing         -> case ws of
                       []  -> ([], Nothing)
                       [w] -> ([], Just $ Right w)
                       ws  -> ([], Just $ Left (length ws, packBytes ws))

scanByte# :: Word8 -> Parser r e ()
scanByte# (W8# c) = Parser \r s ->
  case indexWord8OffAddr# s 0# of
    c' -> case eqWord# c c' of
      1# -> OK# () (plusAddr# s 1#)
      _  -> Err# Default s
{-# inline scanByte# #-}

ensureBytes# :: Int -> Parser r e ()
ensureBytes# (I# len) = Parser \(# eob, _ #) s ->
  case len <=# minusAddr# eob s of
    1# -> OK# () s
    _  -> Err# Default s
{-# inline ensureBytes# #-}

scanWord# :: Word -> Parser r e ()
scanWord# (W# w) = Parser \r s ->
  case indexWordOffAddr# s 0# of
    w' -> case eqWord# w w' of
      1# -> OK# () (plusAddr# s 8#)
      _  -> Err# Default s
{-# inline scanWord# #-}

-- | TODO: remove possible out-of-bound memory access!
scanPartialWord# :: Int -> Word -> Parser r e ()
scanPartialWord# (I# len) (W# w) = Parser \r s ->
  case indexWordOffAddr# s 0# of
    w' -> case uncheckedIShiftL# (8# -# len) 3# of
      sh -> case uncheckedShiftL# w' sh of
        w' -> case uncheckedShiftRL# w' sh of
          w' -> case eqWord# w w' of
            1# -> OK# () (plusAddr# s len)
            _  -> Err# Default s

string :: String -> Q Exp
string str = do
  let (w8s, end)  = vectorize $ strToBytes str
      len         = 8 * length w8s + maybe 0 (either fst (const 1)) end
      go []       = maybe ([| pure () |])
                          (either (\(n, w) -> [| scanPartialWord# n w |])
                                  (\w -> [| scanByte# w |]))
                          end
      go (w8:w8s) = [| scanWord# w8 >> $(go w8s) |]
  [| ensureBytes# len >> $(go w8s) |]

char :: Char -> Q Exp
char c = string [c]
