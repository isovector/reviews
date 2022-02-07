{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module BialgebraSorting where

import Data.Maybe
import Prelude hiding (swap, foldr)
import Data.List (insert, unfoldr, delete)
import Control.Arrow ((&&&))


insertSort :: Ord a => [a] -> [a]
insertSort = foldr insert []

selectSort :: forall a. Ord a => [a] -> [a]
selectSort = unfoldr select
  where
    select :: [a] -> Maybe (a, [a])
    select [] = Nothing
    select as =
      let x = minimum as
          xs = delete x as
       in Just (x, xs)

newtype Mu f = Mu { unMu :: f (Mu f) }

instance Show (f (Mu f)) => Show (Mu f) where
  showsPrec n (Mu f) = showsPrec n f

data Tag = UnsortedTag | SortedTag

data ListF (t :: Tag) a k = Nil | a :> k
  deriving (Eq, Ord, Show, Functor)

infixr 5 :>

type Unsorted = ListF 'UnsortedTag
type Sorted = ListF 'SortedTag

cata :: Functor f => (f a -> a) -> Mu f -> a
cata f = f . fmap (cata f) . unMu

newtype Nu f = Nu
  { unNu :: f (Nu f)
  }

instance Show (f (Nu f)) => Show (Nu f) where
  showsPrec n (Nu f) = showsPrec n f

ana :: Functor f => (a -> f a) -> a -> Nu f
ana f = Nu . fmap (ana f) . f

in0 :: Functor f => Mu f -> f (Mu f)
in0 = cata (fmap Mu)

out0 :: Functor f => f (Nu f) -> Nu f
out0 = ana (fmap unNu)

downcast :: Functor f => Nu f -> Mu f
downcast = Mu . fmap downcast . unNu

upcast :: Functor f => Mu f -> Nu f
upcast = cata out0  -- or: ana in0


type SortingFunc a = Ord a => Mu (Unsorted a) -> Nu (Sorted a)

bubbleSort' :: SortingFunc a
bubbleSort' = ana $ cata bub

bub
    :: Ord a
    => Unsorted a (Sorted a (Mu (Unsorted a)))
    -> Sorted a (Mu (Unsorted a))
bub Nil = Nil
bub (a :> Nil) = a :> Mu Nil
bub (a :> b :> x)
  | a <= b = a :> Mu (b :> x)
  | otherwise = b :> Mu (a :> x)


naiveInsertSort :: SortingFunc a
naiveInsertSort = cata (ana naiveIns)

naiveIns :: Ord a => Unsorted a (Nu (Sorted a)) -> Sorted a (Unsorted a (Nu (Sorted a)))
naiveIns Nil = Nil
naiveIns (a :> Nu Nil) = a :> Nil
naiveIns (a :> Nu (b :> x))
  | a <= b = a :> b :> x
  | otherwise = b :> a :> x

swap :: Ord a => Unsorted a (Sorted a x) -> Sorted a (Unsorted a x)
swap Nil = Nil
swap (a :> Nil) = a :> Nil
swap (a :> b :> x)
  | a <= b    = a :> b :> x
  | otherwise = b :> a :> x

bubbleSort'' :: SortingFunc a
bubbleSort'' = ana $ cata $ fmap Mu . swap

naiveInsertSort'' :: SortingFunc a
naiveInsertSort'' = cata $ ana $ swap . fmap unNu

-- its not clear to me why these would be bubble or insertion sort


-- section 3.4

-- law:
--
-- bubble . in = bub . map bubble
-- fold bub . in = bub . map (fold bub)
--
-- this comes for free from the UMP of the initial algebra:
-- fold f . in  ≡ f . map (fold f)
--
-- bub is fmap in . swap
-- so
--
-- bubble . in = fmap in . swap . map bubble

para :: Functor f => (f (Mu f, a) -> a) -> Mu f -> a
para f = f . fmap (id &&& para f) . unMu

apo :: Functor f => (a -> f (Either (Nu f) a)) -> a -> Nu f
apo f = Nu . fmap (either id (apo f)) . f

insertSort' :: SortingFunc a
insertSort' = cata (apo ins)

ins
    :: Ord a
    => Unsorted a (Nu (Sorted a))
    -> Sorted a (Either (Nu (Sorted a))
                        (Unsorted a (Nu (Sorted a))))
ins Nil = Nil
ins (a :> Nu Nil) = a :> Left (Nu Nil)
ins (a :> Nu (b :> x))
  | a <= b = a :> Left (Nu (b :> x))
  | otherwise = b :> Right (a :> x)

sel
    :: Ord a
    => Unsorted a ( Mu (Unsorted a)
                  , Sorted a (Mu (Unsorted a))
                  )
    -> Sorted a (Mu (Unsorted a))
sel Nil                  = Nil
sel (a :> (x, Nil))      = a :> x
sel (a :> (x, b :> x'))
  | a <= b               = a :> x
  | otherwise            = b :> Mu (a :> x')

toMu :: [a] -> Mu (Unsorted a)
toMu = foldr ((Mu .) . (:>)) (Mu Nil)

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ b [] = b
foldr fabb b (a : as') = fabb a (foldr fabb b as')

fromNu :: Nu (Sorted a) -> [a]
fromNu = unfoldr $ \ (Nu sf) ->
  case sf of
    Nil       -> Nothing
    a :> nu -> Just (a, nu)

swop :: Ord a => Unsorted a (x, Sorted a x) -> Sorted a (Either x (Unsorted a x))
swop Nil = Nil
swop (a :> (x, Nil)) = a :> (Left x)
swop (a :> (x, (b :> x')))
  | a <= b    = a :> Left x
  | otherwise = b :> Right (a :> x')

insertSort'' :: SortingFunc a
insertSort'' = cata . apo $ swop . fmap (id &&& unNu)

selectSort' :: SortingFunc a
selectSort' = ana . para $ fmap (either id Mu) . swop

data Tree a k = Empty | Node k a k
  deriving (Eq, Ord, Show, Functor)

pivot :: Ord a => Unsorted a (Tree a (Mu (Unsorted a))) -> Tree a (Mu (Unsorted a))
pivot Nil = Empty
pivot (a :> Empty) = Node (Mu Nil) a (Mu Nil)
pivot (a :> Node l b r)
  | a <= b = Node (Mu (a :> l)) b r
  | otherwise = Node l b (Mu (a :> r))

sprout :: Ord a => Unsorted a (x, Tree a x) -> Tree a (Either x (Unsorted a x))
sprout Nil = Empty
sprout (a :> (x, Empty)) = Node (Left x) a (Left x)
sprout (a :> (x, (Node l b r)))
  | a <= b = Node (Right (a :> l)) b (Left r)
  | otherwise = Node (Left l) b (Right (a :> r))

wither
    :: Tree a (x, Sorted a x)
    -> Sorted a (Either x (Tree a x))
wither Empty = Nil
wither (Node (_, Nil) a (r, _)) = a :> (Left r)
wither (Node (_, b :> l') a (r, _)) = b :> Right (Node l' a r)

grow :: Ord a => Mu (Unsorted a) -> Nu (Tree a)
grow = cata $ apo $ sprout . fmap (id &&& unNu)

grow' :: Ord a => Mu (Unsorted a) -> Nu (Tree a)
grow' = ana $ para $ fmap (either id Mu) . sprout

flatten :: Mu (Tree a) -> Nu (Sorted a)
flatten = cata $ apo $ wither . fmap (id &&& unNu)

flatten' :: Mu (Tree a) -> Nu (Sorted a)
flatten' = cata $ apo $ wither . fmap (id &&& unNu)

quickTree :: SortingFunc a
quickTree = flatten . downcast . grow'

treeQuick :: SortingFunc a
treeQuick = flatten' . downcast . grow

runSort :: Ord a => SortingFunc a -> [a] -> [a]
runSort f = fromNu . f . toMu

quickSort, treeSort :: SortingFunc a
quickSort = flatten  . downcast . grow
treeSort  = flatten' . downcast . grow'

big :: [Int]
big = [0..1024]

