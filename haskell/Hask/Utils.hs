module Hask.Utils where

import Data.Char
import Data.List as L
import Data.IntMap as M
import Debug.Trace

trace :: [Int] -> a -> a
trace = Debug.Trace.trace . L.map chr

intMap_mergeWithKey'
    :: (Int -> a -> b -> Maybe c)
    -> ([(Int, a)] -> [(Int, c)])
    -> ([(Int, b)] -> [(Int, c)])
    -> ([(Int, a)]) -> ([(Int, b)])
    -> [(Int, c)]
intMap_mergeWithKey' combine only1 only2 m1 m2 =
    M.toList $ M.mergeWithKey combine
        (M.fromList . only1 . M.toList)
        (M.fromList . only2 . M.toList)
        (M.fromList m1) (M.fromList m2)

uncons :: [a] -> Maybe (a, [a])
uncons [] = Nothing
uncons (x:xs) = Just (x, xs)

-- Used for conversions between vectors and seq, which are the same in Haskell
vec_id :: Int -> a -> a
vec_id _ = id

vshiftin :: Int -> [a] -> a -> [a]
vshiftin _ xs x = xs ++ [x]

vreplace :: Int -> [a] -> Int -> a -> [a]
vreplace _ xs n x = take n xs ++ x : drop (n+1) xs

vmap :: Int -> (a -> b) -> [a] -> [b]
vmap _ = L.map

vfoldl' :: Int -> (b -> a -> b) -> b -> [a] -> b
vfoldl' _ = L.foldl'

vfoldl'_with_index :: Int -> (Int -> b -> a -> b) -> b -> [a] -> b
vfoldl'_with_index _ f = go 0
  where
    go _ z [] = z
    go n z (x:xs) = go (n+1) (f n z x) xs

vmap_with_index :: Int -> (Int -> a -> b) -> [a] -> [b]
vmap_with_index _ f = go 0
  where
    go _ [] = []
    go n (x:xs) = f n x : go (n+1) xs

vnth :: Int -> [a] -> Int -> a
vnth _ = (!!)

vec_rect :: b -> (Int -> a -> [a] -> b -> b) -> Int -> [a] -> b
vec_rect z f _ = go z
  where
    go z [] = z
    go z (x:xs) = go (f err x xs z) xs

    err = error "list_rect: attempt to use size"
