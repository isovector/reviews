{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
module BialgebraSorting.Scratch where

import BialgebraSorting ( Nu(..), Mu(..), cata, ana, downcast, para, apo)
import Debug.Trace (traceShowId, traceId, trace)
import Data.Typeable
import Control.Arrow ((&&&))
import Data.Tuple (swap)

-- ok, so how the heck does an ana . cata work?


data Sorted a k = SNil | a :! k
  deriving (Eq, Ord, Show, Functor)

data Unsorted a k = UNil | a :> k
  deriving (Eq, Ord, Show, Functor)

infixr 5 :>
infixr 5 :!

anacata :: (Functor up, Functor down, Show (up (Mu down)))
     => ( down (up (Mu down))
       ->       up (Mu down)
        )
     -> Mu down
     -> Nu up
anacata f = ana $ traceX "new" . cata f
-- main = anacat @Int [3,1,4,2]
-- seed : UNil
-- res  : SNil
--
-- seed : 2 :> SNil
-- res  : 2 :! UNil
--
-- seed : 4 :> (2 :! UNil)
-- res  : 2 :! (4 :> UNil)
--
-- seed : 1 :> (2 :! (4 :> UNil))
-- res  : 1 :! (2 :> (4 :> UNil))
--
-- seed : 3 :> (1 :! (2 :> (4 :> UNil)))
-- res  : 1 :! (3 :> (2 :> (4 :> UNil)))
--
--
--
-- new : 1 :! (3 :> (2 :> (4 :> UNil)))
-- seed : UNil
-- res  : SNil
-- seed : 4 :> SNil
-- res  : 4 :! UNil
--
-- seed : 2 :> (4 :! UNil)
-- res  : 2 :! (4 :> UNil)
-- seed : 3 :> (2 :! (4 :> UNil))
-- res  : 2 :! (3 :> (4 :> UNil))
--
--
--
-- new : 2 :! (3 :> (4 :> UNil))
-- seed : UNil
-- res  : SNil
-- seed : 4 :> SNil
-- res  : 4 :! UNil
--
-- seed : 3 :> (4 :! UNil)
-- res  : 3 :! (4 :> UNil)
--
-- new : 3 :! (4 :> UNil)
-- seed : UNil
-- res  : SNil
-- seed : 4 :> SNil
-- res  : 4 :! UNil
-- new : 4 :! UNil
-- seed : UNil
-- res  : SNil
-- new : SNil
--
-- so WHATS HAPPENING HERE?
--
-- the given list is cata'd, moving the smallest element to the front
-- leaving the rest of the list in its original order
--
-- this results in 1 :! (3 :> (2 :> (4 :> UNil))
-- the 1 is the beginning of our new list
-- and the tail is the next term getting cata'd
--
-- then 2 :! (3 :> (4 :> UNil))
-- and continue until it's done!

cataana f = cata $ traceX "new" . ana f

cataapo f = cata $ traceX "new" . apo f

anapara
    :: (Show (up (Mu down)), Functor up, Functor down)
    => (down (Mu down
             , up (Mu down)
             )
      -> up (Mu down)
       )
    -> Mu down
    -> Nu up
anapara f = ana $ traceX "new" . para f
-- seed : UNil
-- res  : SNil
-- seed : 2 :> (SNil,UNil)
-- res  : 2 :! Left UNil
-- done : UNil
-- seed : 4 :> (2 :! UNil,2 :> UNil)
-- res  : 2 :! Right (4 :> UNil)
-- seed : 1 :> (2 :! (4 :> UNil),4 :> (2 :> UNil))
-- res  : 1 :! Left (4 :> (2 :> UNil))
-- done : 4 :> (2 :> UNil)
-- seed : 3 :> (1 :! (4 :> (2 :> UNil)),1 :> (4 :> (2 :> UNil)))
-- res  : 1 :! Right (3 :> (4 :> (2 :> UNil)))
--
-- new : 1 :! (3 :> (4 :> (2 :> UNil)))
-- seed : UNil
-- res  : SNil
-- seed : 2 :> (SNil,UNil)
-- res  : 2 :! Left UNil
-- done : UNil
-- seed : 4 :> (2 :! UNil,2 :> UNil)
-- res  : 2 :! Right (4 :> UNil)
-- seed : 3 :> (2 :! (4 :> UNil),4 :> (2 :> UNil))
-- res  : 2 :! Right (3 :> (4 :> UNil))
--
-- new : 2 :! (3 :> (4 :> UNil))
-- seed : UNil
-- res  : SNil
-- seed : 4 :> (SNil,UNil)
-- res  : 4 :! Left UNil
-- done : UNil
-- seed : 3 :> (4 :! UNil,4 :> UNil)
-- res  : 3 :! Left (4 :> UNil)
-- done : 4 :> UNil
--
-- new : 3 :! (4 :> UNil)
-- seed : UNil
-- res  : SNil
-- seed : 4 :> (SNil,UNil)
-- res  : 4 :! Left UNil
-- done : UNil
-- new : 4 :! UNil
-- seed : UNil
-- res  : SNil
-- new : SNil
--
-- so wtf?
-- the cache `c` is the UNSORTED TAIL OF THE LIST
-- if the new unsorted head is smaller than the sorted head,
-- then this unsorted head is the smallest element we've seen so far
-- and we can just give it back
--
-- but what value do we get from reusing the tail?
--
-- is the value here laziness? we dont need to construct the tailif we
-- are just sharing it
--
--


susIns :: Ord a => Unsorted a (c, Sorted a x) -> Sorted a (Either c (Unsorted a x))
susIns UNil = SNil
susIns (a :> (x, SNil)) = a :! Right UNil
susIns (a :> (x, b :! x'))
  | a <= b    = a :! Right (b :> x')
  | otherwise = b :! Right (a :> x')

ins' :: Ord a => Unsorted a (c, Sorted a x) -> Sorted a (Either c (Unsorted a x))
ins' UNil = SNil
ins' (a :> (x, SNil)) = a :! Left x
ins' (a :> (x, b :! x'))
  | a <= b    = a :! Left x
  | otherwise = b :! Right (a :> x')

ins :: Ord a => Unsorted a (Sorted a x) -> Sorted a (Unsorted a x)
ins UNil = SNil
ins (a :> SNil) = a :! UNil
ins (a :> b :! x)
  | a <= b    = a :! b :> x
  | otherwise = b :! a :> x

traceX :: (Show a) => String -> a -> a
traceX s a = a
  -- trace ( unwords [s
  --                  -- , "@"
  --                  -- , show $ typeOf a
  --                  , ":"
  --                  , show a
  --                  ]) a

traceFX :: (Show b) => String -> (a -> b) -> a -> a
traceFX s f a = a
  -- trace ( unwords [s
  --                  -- , "@"
  --                  -- , show $ typeOf a
  --                  , ":"
  --                  , show $ f a
  --                  ]) a

len :: Nu (Sorted a) -> Int
len = cata (\case
                SNil -> 0
                _ :! n -> 1 + n
            )
    . downcast

toList :: Nu (Sorted a) -> [a]
toList = cata (\case
                SNil -> []
                a :! n -> a : n
            )
    . downcast

anapar :: (Ord a, Show a, Typeable a) => [a] -> [a]
anapar = toList
       . anapara ( fmap (either id Mu)
                 . traceX "res "
                 . ins'
                 . traceFX "seed" (fmap swap)
                 ) . toMu

anasus :: (Ord a, Show a, Typeable a) => [a] -> [a]
anasus = toList
       . anapara ( fmap (either id Mu)
                 . traceX "res "
                 . susIns
                 . traceFX "seed" (fmap swap)
                 ) . toMu

anacat :: (Ord a, Show a, Typeable a) => [a] -> [a]
anacat = toList
       . anacata (fmap Mu . traceX "res "
                          . ins
                          . traceX "seed") . toMu

catana :: (Ord a, Show a, Typeable a) => [a] -> [a]
catana = toList
       . cataana (traceX "res "
                          . ins
                          . traceX "seed" . fmap unNu) . toMu

catapo :: (Ord a, Show a, Typeable a) => [a] -> [a]
catapo = toList
       . cataapo (traceX "res "
                          . ins'
                          . traceX "seed" . fmap (id &&& unNu)) . toMu


catsus :: (Ord a, Show a, Typeable a) => [a] -> [a]
catsus = toList
       . cataapo (traceX "res "
                          . susIns
                          . traceX "seed" . fmap (id &&& unNu)) . toMu
toMu :: [a] -> Mu (Unsorted a)
toMu = foldr ((Mu .) . (:>)) (Mu UNil)

