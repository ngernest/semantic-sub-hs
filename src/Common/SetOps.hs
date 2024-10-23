{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Avoid lambda" #-}
module Common.SetOps
  ( subsets,
    strictSubsets,
    nonEmptySubsets,
  )
where

import Data.List (delete)

-- | Powerset of a list
subsets :: (Eq x) => [x] -> [[x]]
subsets [] = [[]]
subsets (x : xs) = map (\ys -> x : ys) xss ++ xss
  where
    xss = subsets xs

-- | Powerset of a list minus original list
-- (i.e. all the strict subsets)
strictSubsets :: (Eq x) => [x] -> [[x]]
strictSubsets xs = delete xs (subsets xs)

-- | Powerset of a list minus the empty list
-- (i.e. all the strict subsets)
nonEmptySubsets :: (Eq x) => [x] -> [[x]]
nonEmptySubsets xs = delete [] (subsets xs)
