{-# LANGUAGE TypeApplications #-}

module Main where

import BialgebraSorting.Scratch
import Criterion.Main
import Test.QuickCheck
import Data.Traversable (for)
import Data.List (sort)
import BialgebraSorting (quickSort, treeSort, quickTree, treeQuick)

main :: IO ()
main = do
  (defaultMain =<<) $
    for [100000, 200000, 400000, 800000] $ \size -> do
      let fwd = [1 .. size]
      shuffled <- generate (shuffle fwd)
      pure $ bgroup (show size)
        [ bench "sort" $ whnf (sort @Int) shuffled
        , bench "bubble" $ whnf (anacat @Int) shuffled
        , bench "selection" $ whnf (anapar @Int) shuffled
        , bench "selection no caching" $ whnf (anasus @Int) shuffled
        , bench "naive insertion" $ whnf (catana @Int) shuffled
        , bench "insertion" $ whnf (catapo @Int) shuffled
        , bench "insertion no caching" $ whnf (catsus @Int) shuffled
        , bench "quicksort" $ whnf (quickSort @Int) shuffled
        , bench "treesort" $ whnf (treeSort @Int) shuffled
        , bench "quickTree" $ whnf (quickTree @Int) shuffled
        , bench "treeQuick" $ whnf (treeQuick @Int) shuffled
        ]

