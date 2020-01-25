{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

import Prelude hiding (id)

id :: forall (a :: *). a -> a
id x = x

majom = 100022

foo = id @Bool True
