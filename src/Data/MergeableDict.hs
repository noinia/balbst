module Data.MergeableDict where

import Prelude hiding (join)

import Control.Applicative(pure, (<$>),(<*>))

import Data.Foldable(Foldable)
import Data.Traversable

import qualified Data.Foldable as F

--------------------------------------------------------------------------------

-- | Mergeable dictionaries based on red black trees


-- Red black trees
data Color = Red | Black deriving (Show,Eq)
type BlackHeight = Int

data RBTree a = Leaf | Node !Color !BlackHeight !(RBTree a) a !(RBTree a)
              deriving (Show,Eq)

instance Functor RBTree where
  fmap = fmapDefault

instance Foldable RBTree where
  foldMap = foldMapDefault

instance Traversable RBTree where
  traverse _ Leaf             = pure Leaf
  traverse f (Node c h l x r) = (\l' x' r' -> Node c h l' x' r') <$> traverse f l
                                                                 <*> f x
                                                                 <*> traverse f r

--------------------------------------------------------------------------------

empty :: RBTree a
empty = Leaf
singleton :: Ord a => a -> RBTree a
singleton = flip insert empty


insert   :: Ord a => a -> RBTree a -> RBTree a
insert x = blacken . insertRB' x


-- | Splits the tree at x; left is everything < x, right > x
--  if x occurs in the tree it is simply deleted.
--
-- running time: O(log n) amortized
split :: Ord a => a -> RBTree a -> (RBTree a, RBTree a)
split x t = let (l,r) = split' x t in (blacken l, blacken r)


-- | Concatenates two trees:
--
-- running time: O(log n) amortized
join        :: Ord a => RBTree a -> RBTree a -> RBTree a
join l Leaf = l
join l    r = let (mr,r') = extractMin' r
              in join' l mr r'

-- Merges two trees. The value ranges of both trees are allowed to overlap.
--
-- running time: O(log^2 n) amortized
merge        :: Ord a => RBTree a -> RBTree a -> RBTree a
merge Leaf tb = tb
merge ta   tb = let (ma,ta') = extractMin' ta
                    (lb,rb)  = split ma tb
                in join' lb ma (rb `merge` ta')

--------------------------------------------------------------------------------
-- | Helper functions


blacken :: RBTree a -> RBTree a
blacken (Node Red h l x r) = Node Black (h+1) l x r
blacken n                  = n


blackHeight :: RBTree t -> BlackHeight
blackHeight Leaf             = 0
blackHeight (Node _ h _ _ _) = h

----------------------------------------
-- | Insert

insertRB' :: Ord a => a -> RBTree a -> RBTree a
insertRB' x Leaf = Node Red 0 Leaf x Leaf
insertRB' x (Node c h l y r)
  | x <= y    = balance c h (insertRB' x l) y r
  | otherwise = balance c h l y (insertRB' x r)


----------------------------------------
-- | Splitting

split'        :: Ord a => a -> RBTree a -> (RBTree a, RBTree a)
split' x Leaf = (Leaf,Leaf)
split' x (Node c h l y r)
  | x == y    = (l,r)
  | x <  y    = let (ll,lr) = split' x l in (ll,join' lr y r)
  | otherwise = let (rl,rr) = split' x r in (join' l y rl,rr)

----------------------------------------
-- | Joining

-- | Joins two trees with in the middle element m
join' :: Ord a => RBTree a -> a -> RBTree a -> RBTree a
join' l m r
  | blackHeight l >= blackHeight r = joinL l m r
  | otherwise                      = joinR l m r

-- pre: Blackheight left >= blackHeight r
joinL                         :: RBTree a -> a -> RBTree a -> RBTree a
joinL Leaf               m rr = balance Red 0 Leaf m rr
joinL n@(Node c h l x r) m rr
  | h == blackHeight rr = balance Red h n m rr
  | otherwise           = balance c   h l x (joinL r m rr)

joinR            :: RBTree a -> a -> RBTree a -> RBTree a
joinR ll  m Leaf = balance Red 0 ll m Leaf
joinR ll m n@(Node c h l x r)
  | h == blackHeight ll = balance Red h ll             m n
  | otherwise           = balance c   h (joinR ll m l) x r

----------------------------------------
-- | Merging

extractMin'                     :: Ord a => RBTree a -> (a, RBTree a)
extractMin' (Node _ _ Leaf x r) = (x, r)
extractMin' (Node c h l    x r) = (\l' -> join' l' x r) <$> extractMin' l

--------------------------------------------------------------------------------
-- | Rebalancing code

balance  :: Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balance Black h (Node Red _ (Node Red _ a x b) y c) z d = node h a x b y c z d
balance Black h (Node Red _ a x (Node Red _ b y c)) z d = node h a x b y c z d
balance Black h a x (Node Red _ (Node Red _ b y c) z d) = node h a x b y c z d
balance Black h a x (Node Red _ b y (Node Red _ c z d)) = node h a x b y c z d
balance co h a x b = Node co h a x b

node h a x b y c z d = Node Red h (Node Black h a x b) y (Node Black h c z d)


--------------------------------------------------------------------------------

fromList :: Ord a => [a] -> RBTree a
fromList = F.foldr insert empty

test' = foldr1 merge $ map singleton [1, 5, 2, 3, 4, 10, 7]
