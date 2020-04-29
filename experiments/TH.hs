{-# language TemplateHaskell #-}

import Language.Haskell.TH
import THPre

import Control.Monad

f = $(do
  nm1 <- newName "x"
  let nm2 = mkName "x"
  return (LamE [VarP nm1] (LamE [VarP nm2] (VarE nm1)))
 )


bar = $$(  foo   )

-- tmap :: Int -> Int -> Q Exp
tmap i n = do
    f <- newName "f"
    as <- replicateM n (newName "a")
    lamE [varP f, tupP (map varP as)] $
        tupE [  if i == i'
                    then [| $(varE f) $a |]
                    else a
               | (a,i') <- map varE as `zip` [1..] ]
