
module ElabState where

import IO
import qualified Data.Array.Dynamic.L as D
import qualified Data.Array.LM        as A
import qualified Data.ByteString      as B

import Common
import Syntax
import Value



-- Top scope
--------------------------------------------------------------------------------

data TopEntry
  = TEDef ~Val ~VTy Tm (Maybe Ty) B.ByteString
  | TEPostulate ~VTy Ty B.ByteString

-- TODO: we'll implement top resizing and allocation later
topSize :: Int
topSize = 50000

top :: A.Array TopEntry
top = runIO (A.new topSize (error "top: undefined entry"))
{-# noinline top #-}

readTop :: Lvl -> IO TopEntry
readTop (Lvl x) | 0 <= x && x < topSize = A.read top x
                | otherwise             = error "index out of bounds"
{-# inline readTop #-}

-- Metacontext
--------------------------------------------------------------------------------

data MetaEntry
  = MEUnsolved ~VTy U
  | MESolved Val

metaCxt :: D.Array MetaEntry
metaCxt = runIO D.empty
{-# noinline metaCxt #-}

readMeta :: Meta -> IO MetaEntry
readMeta (Meta i) = D.read metaCxt i
{-# inline readMeta #-}

newMeta :: VTy -> U -> IO Meta
newMeta ~a u = do
  s <- D.size metaCxt
  D.push metaCxt (MEUnsolved a u)
  pure (Meta s)
{-# inline newMeta #-}

-- Universe metacontext
--------------------------------------------------------------------------------

uCxt :: D.Array (Maybe U)
uCxt = runIO D.empty
{-# noinline uCxt #-}

readUMeta :: UMeta -> IO (Maybe U)
readUMeta (UMeta i) = D.read uCxt i
{-# inline readUMeta #-}

newUMeta :: IO UMeta
newUMeta = do
  s <- D.size uCxt
  D.push uCxt Nothing
  pure (UMeta s)
{-# inline newUMeta #-}
