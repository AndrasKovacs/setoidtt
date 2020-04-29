{-# language TemplateHaskell #-}

module THPre where

import Language.Haskell.TH

foo = [|| 10 + 300 ||]

-- printf :: String -> Q Exp
-- printf "" = [| \x ->
