
{-# language MagicHash, UnboxedTuples, BangPatterns #-}

module Cmm where

import GHC.Exts
import GHC.Prim

foo f g s = catch# f g s



-- data S a = S {unS :: !a}

-- data Tree = Node !Tree !Tree | Leaf !Int

-- inc :: S Tree -> Tree
-- inc (S t) = case t of
--   Leaf n   -> Leaf (n + 1)
--   Node l r -> Node (inc (S l)) (inc (S r))

-- test :: Int -> State# s -> (# State# s, ByteArray# #)
-- test (I# n) s = case newByteArray# n s of
--   (# s, marr #) -> unsafeFreezeByteArray# marr s


-- test2 = unsafeFreezeByteArray#

-- test3 f x = f (f x)

-- test4 s = case newByteArray# 16# s of
--   (# s, marr1 #) -> case newByteArray# 16# s of
--     (# s, marr2 #) -> (# s, marr1, marr2 #)

-- data Foo = F | G | H | I | J | K | L | A | B | C | D | E

-- f A = B
-- f B = C
-- f C = D
-- f D = E
-- f E = F
-- f F = G
-- f G = H
-- f H = I
-- f I = J
-- f J = K
-- f K = L
-- f L = A

-- data Foo = Foo | Bar

-- f :: Foo -> Foo -> Foo
-- f x y = x





-- data S a = S {unS :: a}

-- data Tree = Node Tree Tree | Leaf Int#

-- foo :: S Tree -> S Bool -> S Tree
-- foo (S t) b = case t of
--   Leaf n -> if unS b then S (Leaf n) else S (Leaf (n +# 1#))
--   Node l r -> S (Node (unS (foo (S l) b)) (unS (foo (S l) b)))






-- sub :: Tree -> (Int# -> Tree) -> Tree
-- sub (Node l r) ~f = Node (sub2 l f) (sub2 r f)
-- sub (Leaf n)   f  = f n

-- sub2 :: Tree -> (Int# -> Tree) -> Tree
-- sub2 (Node l r) ~f = Node (sub l f) (sub r f)
-- sub2 (Leaf n)   f  = f (n +# 1#)

-- inc2 :: S Tree -> S Tree
-- inc2 (S t) = case t of
--   Node l r -> S (Node (unS (inc2 (S l))) (unS (inc2 (S r))))
--   Leaf n   -> S (Leaf (n + 1))
