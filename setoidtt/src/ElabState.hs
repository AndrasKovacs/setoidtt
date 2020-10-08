
module ElabState where

import IO
import qualified Data.Array.Dynamic.L as D
import qualified Data.Array.LM        as A
import qualified Data.ByteString      as B

import Common
import qualified Syntax as S
import qualified Value as V



-- Top scope
--------------------------------------------------------------------------------

data TopEntry
  = TEDef ~V.Val ~V.Ty S.Tm (Maybe S.Ty) B.ByteString
  | TEPostulate ~V.Ty S.Ty B.ByteString

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
  = MEUnsolved ~V.WTy S.U
  | MESolved V.Val

metaCxt :: D.Array MetaEntry
metaCxt = runIO D.empty
{-# noinline metaCxt #-}

readMeta :: Meta -> IO MetaEntry
readMeta (Meta i) = D.read metaCxt i
{-# inline readMeta #-}

newMeta :: V.WTy -> S.U -> IO Meta
newMeta ~a u = do
  s <- D.size metaCxt
  D.push metaCxt (MEUnsolved a u)
  pure (Meta s)
{-# inline newMeta #-}

-- Universe metacontext
--------------------------------------------------------------------------------

uCxt :: D.Array (Maybe S.U)
uCxt = runIO D.empty
{-# noinline uCxt #-}

readUMeta :: UMeta -> IO (Maybe S.U)
readUMeta (UMeta i) = D.read uCxt i
{-# inline readUMeta #-}

newUMeta :: IO UMeta
newUMeta = do
  s <- D.size uCxt
  D.push uCxt Nothing
  pure (UMeta s)
{-# inline newUMeta #-}
