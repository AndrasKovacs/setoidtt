{-# language OverloadedStrings, BangPatterns #-}

module TextOps where

import Data.Text
import Control.Monad

-- Text is crap for fast parsing, just look at the core..
foo :: Text -> Bool
foo t = Data.Text.take 3 t == "foo"

-- foo :: Text -> Maybe ()
-- foo t = do
--   (c, t) <- uncons t
--   guard (c == 'f')
--   (c, t) <- uncons t
--   guard (c == 'o')
--   (c, t) <- uncons t
--   guard (c == 'o')
--   pure ()
