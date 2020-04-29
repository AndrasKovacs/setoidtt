
{-# language NoStrict #-}
-- we do this because pattern synonyms are made strict by Strict, and there is no way
-- to make them lazy AFAIK.

module Parser.Internal2 where

import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as B

import Data.Bits
import Data.Char (ord)
import Data.Word
import GHC.Exts

import IO

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

instance Monad (Parser r e) where
  return = pure
  {-# inline return #-}
  Parser fa >>= f = Parser \r s -> case fa r s of
    Err# e s -> Err# e s
    OK# a s  -> runParser# (f a) r s
  {-# inline (>>=) #-}

ask :: Parser r e r
ask = Parser \(# _, r #) s -> OK# r s
{-# inline ask #-}

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
            let resc = (ord# c1 -# 0xC0# `uncheckedIShiftL#` 6#) `orI#`
                       (ord# c2 -# 0x80#)
            in OK# (C# (chr# resc)) (plusAddr# buf 2#)
          _ -> case indexCharOffAddr# buf 2# of
            c3 -> case c1 `leChar#` '\xEF'# of
              1# ->
                let resc = ((ord# c1 -# 0xE0#) `uncheckedIShiftL#` 12#) `orI#`
                           ((ord# c2 -# 0x80#) `uncheckedIShiftL#`  6#) `orI#`
                           ( ord# c3 -# 0x80#)
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

char :: Char -> Parser r e ()
char c = () <$ satisfy (Char c) (==c)
{-# inline char #-}

string :: String -> Parser r e ()
string str = go str <|> err (String str) where
  go []     = pure ()
  go (c:cs) = char c >> go cs
  {-# noinline go #-}
{-# inline string #-}

charL1 :: Char -> Parser r e ()
charL1 (C# c) = Parser \(# eob, i #) buf ->
  case eqAddr# eob buf of
    1# -> Err# (Char (C# c)) buf
    _  -> case derefChar# buf of
      c1 -> case c1 `eqChar#` c of
        1# -> OK# () (plusAddr# buf 1#)
        _  -> Err# (Char (C# c)) buf
{-# inline charL1 #-}

stringL1 :: String -> Parser r e ()
stringL1 str = go str <|> err (String str) where
  go []     = pure ()
  go (c:cs) = charL1 c >> go cs
  {-# noinline go #-}
{-# inline stringL1 #-}

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

silent :: Parser r e a -> Parser r e a
silent pa = Parser \r s -> case runParser# pa r s of
  Err# e s -> Err# Default s
  x        -> x
{-# inline silent #-}

data Res e a = OK a B.ByteString | Err (Error e) B.ByteString
  deriving Show

runParser :: Parser r e a -> r -> B.ByteString -> Res e a
runParser (Parser f) r b = runIO do
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
{-# inline runParser #-}

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

--------------------------------------------------------------------------------

-- -- getPos :: Parser e Int
-- -- getPos = Parser \(# eob, _ #) s -> OK# (I# (minusAddr# eob s)) s
-- -- {-# inline getPos #-}

-- -- getIndentation :: Parser e Int
-- -- getIndentation = Parser \(# _, i #) s -> OK# (I# i) s
-- -- {-# inline getIndentation #-}

-- -- indentedAt :: Int -> Parser String a -> Parser String a
-- -- indentedAt i pa = do
-- --   actual <- getIndentation
-- --   unless (actual == i) (err "incorrect indentation")
-- --   _


-- -- indentedAt :: Pos -> Parser a -> Parser a
-- -- indentedAt level p = do


-- -- optional :: Parser e a -> Parser e (Maybe a)
-- -- optional pa = (Just <$> pa) <|> pure Nothing
-- -- {-# rules "stringL12"  forall c1 c2. stringL1 (c1:c2:[]) = charL1 c1 >> charL1 c2 #-}
