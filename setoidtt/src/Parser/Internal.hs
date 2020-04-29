
{-# language NoStrict #-}
-- we do this because pattern synonyms are made strict by Strict, and there is no way
-- to make them lazy AFAIK.

module Parser.Internal where

import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as B

-- import Control.Monad
import Data.Bits
import Data.Char (ord)
import Data.Word
import GHC.Exts
-- import qualified GHC.Unicode

import IO

type Read# = (# Addr#, Int# #) -- end of buffer, indentation level
type Res# e a = (# (# a, Addr# #) | (# e #) #)

pattern OK# :: a -> Addr# -> Res# e a
pattern OK# a s = (# (# a, s #) | #)

pattern Err# :: e -> Res# e a
pattern Err# e = (# | (# e #) #)
{-# complete OK#, Err# #-}

newtype Parser e a = Parser {runParser# :: Read# -> Addr# -> Res# e a}

instance Functor (Parser e) where
  fmap f (Parser g) = Parser \r s -> case g r s of
    OK# a s -> let b = f a in OK# b s
    Err# e  -> Err# e
  {-# inline fmap #-}

err :: e -> Parser e a
err e = Parser \r s -> Err# e
{-# inline err #-}

instance Applicative (Parser e) where
  pure a = Parser \r s -> OK# a s
  {-# inline pure #-}
  Parser ff <*> Parser fa = Parser \r s -> case ff r s of
    Err# e  -> Err# e
    OK# f s -> case fa r s of
      Err# e -> Err# e
      OK# a s -> OK# (f a) s
  {-# inline (<*>) #-}

instance Monad (Parser e) where
  return = pure
  {-# inline return #-}
  Parser fa >>= f = Parser \r s -> case fa r s of
    Err# e -> Err# e
    OK# a s -> runParser# (f a) r s
  {-# inline (>>=) #-}

indentLvl :: Parser e Int
indentLvl = Parser \(# _, i #) s -> OK# (I# i) s
{-# inline indentLvl #-}

derefChar# :: Addr# -> Char#
derefChar# addr = indexCharOffAddr# addr 0#
{-# inline derefChar# #-}

eof :: Parser String ()
eof = Parser \(# eob, _ #) s -> case eqAddr# eob s of
  1# -> OK# () s
  _  -> Err# "expected end of file"
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
(<|>) :: Parser e a -> Parser e a -> Parser e a
(<|>) (Parser f) (Parser g) = Parser \r s ->
  case f r s of
    Err# _ -> g r s
    x      -> x
{-# inline (<|>) #-}

anyCharL1 :: Parser String Char
anyCharL1 = Parser \(# eob, i #) buf -> case eqAddr# eob buf of
  1# -> Err# "expected non-empty input"
  _  -> case derefChar# buf of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# (C# c1) (plusAddr# buf 1#)
      _  -> Err# "expected a latin1 character"
{-# inline anyCharL1 #-}

anyCharL1_ :: Parser String ()
anyCharL1_ = () <$ anyCharL1
{-# inline anyCharL1_ #-}

anyChar :: Parser String Char
anyChar = Parser \(# eob, i #) buf -> case eqAddr# eob buf of
  1# -> Err# "expected non-empty input"
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

anyChar_ :: Parser String ()
anyChar_ = Parser \(# eob, i #) buf -> case eqAddr# eob buf of
  1# -> Err# "expected non-empty input"
  _  -> case derefChar# buf of
    c1 -> case c1 `leChar#` '\x7F'# of
      1# -> OK# () (plusAddr# buf 1#)
      _  -> case c1 `leChar#` '\xDF'# of
          1# -> OK# () (plusAddr# buf 2#)
          _  -> case c1 `leChar#` '\xEF'# of
              1# -> OK# () (plusAddr# buf 3#)
              _ ->  OK# () (plusAddr# buf 4#)
{-# inline anyChar_ #-}

satisfy :: String -> (Char -> Bool) -> Parser String Char
satisfy msg f = (do {c <- anyChar; if f c then pure c else err msg}) <|> err msg
{-#  inline satisfy #-}

satisfyL1 :: String -> (Char -> Bool) -> Parser String Char
satisfyL1 msg f = (do {c <- anyCharL1; if f c then pure c else err msg}) <|> err msg
{-#  inline satisfyL1 #-}

-- alpha :: Parser String Char
-- alpha =
--   let msg = "expected a letter" in
--       satisfyL1 msg (\c -> isLatinLetter c || isGreekLetter c)
--   <|> satisfy msg (\c -> c /= ' ' && c /= '\n' && c /= ')' && c /= '(' && GHC.Unicode.isAlpha c)
-- {-# inline alpha #-}

char :: Char -> Parser String ()
char c = () <$ satisfy ("expected character: "++[c]) (==c)
{-# inline char #-}

string :: String -> Parser String ()
string str = case "expected string: " ++ str of
  msg -> go str <|> err msg where
            go []     = pure ()
            go (c:cs) = char c >> go cs
            {-# noinline go #-}
{-# inline string #-}

charL1 :: Char -> Parser String ()
charL1 (C# c) =
  let msg = "expected character: " ++ [C# c]
  in Parser \(# eob, i #) buf -> case eqAddr# eob buf of
       1# -> Err# "expected non-empty input"
       _  -> case derefChar# buf of
         c1 -> case c1 `eqChar#` c of
           1# -> OK# () (plusAddr# buf 1#)
           _  -> Err# msg
{-# inline charL1 #-}

stringL1 :: String -> Parser String ()
stringL1 str = case "expected string: " ++ str of
  msg -> go str <|> err msg where
            go []     = pure ()
            go (c:cs) = charL1 c >> go cs
            {-# noinline go #-}
{-# inline stringL1 #-}

many_ :: Parser e a -> Parser e ()
many_ (Parser f) = go where
  go = Parser \r s -> case f r s of
    Err# e  -> OK# () s
    OK# a s -> runParser# go r s
{-# inline many_ #-}

some_ :: Parser e a -> Parser e ()
some_ pa = pa >> many_ pa
{-# inline some_ #-}

manyTill_ :: Parser e a -> Parser e b -> Parser e ()
manyTill_ pa end = go where
  go = (() <$ end) <|> (pa >> go)
{-# inline manyTill_ #-}

silent :: Parser String a -> Parser String a
silent pa = Parser \r s -> case runParser# pa r s of
  Err# _ -> Err# ""
  x      -> x
{-# inline silent #-}

data Res e a = OK a B.ByteString | Err e
  deriving Show

runParser :: Parser e a -> B.ByteString -> Res e a
runParser (Parser f) b = runIO do
  B.unsafeUseAsCString b \(Ptr buf) -> do
    let !(I# len) = B.length b
    let end = plusAddr# buf len
    case f (# end, 0# #) buf of
      Err# e  -> pure (Err e)
      OK# a s -> do
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

runParser' :: Parser e a -> String -> Res e a
runParser' p str = runParser p (B.pack (charToBytes =<< str))

--------------------------------------------------------------------------------

-- getPos :: Parser e Int
-- getPos = Parser \(# eob, _ #) s -> OK# (I# (minusAddr# eob s)) s
-- {-# inline getPos #-}

-- getIndentation :: Parser e Int
-- getIndentation = Parser \(# _, i #) s -> OK# (I# i) s
-- {-# inline getIndentation #-}

-- indentedAt :: Int -> Parser String a -> Parser String a
-- indentedAt i pa = do
--   actual <- getIndentation
--   unless (actual == i) (err "incorrect indentation")
--   _


-- indentedAt :: Pos -> Parser a -> Parser a
-- indentedAt level p = do


-- optional :: Parser e a -> Parser e (Maybe a)
-- optional pa = (Just <$> pa) <|> pure Nothing
-- {-# rules "stringL12"  forall c1 c2. stringL1 (c1:c2:[]) = charL1 c1 >> charL1 c2 #-}
