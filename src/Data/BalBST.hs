
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
module Data.BalBST where

import Prelude hiding (foldr,foldl,join)

import Control.Applicative((<$>))
import Data.Semigroup
import Data.Foldable


--------------------------------------------------------------------------------

class Semigroup k => k `IsKeyFor` v | v -> k where
  toKey :: v -> k

  goLeft :: v -> k -> Bool
  goLeft x k = not $ goRight x k
  goRight :: v -> k -> Bool
  goRight x k = not $ goLeft x k

--------------------------------------------------------------------------------

data Color = Red | Black deriving (Show,Eq)

type BlackHeight = Int

data Node k v = Leaf v
              | Node Color (Node k v) BlackHeight k (Node k v)
              deriving (Show,Eq)


instance Foldable (Node k) where
  foldMap f (Leaf v) = f v
  foldMap f (Node _ l _ _ r) = foldMap f l `mappend` foldMap f r




-- > instance (k `IsKeyFor` v) => k `IsKeyFor` (Node k v) where


data BalBST k v = Empty | BalBST (Node k v)
                deriving (Show,Eq)

instance Semigroup k => Foldable (BalBST k) where
  foldMap _ Empty = mempty
  foldMap f (BalBST n) = foldMap f n





blackHeight :: Node k v -> BlackHeight
blackHeight (Leaf _) = 0
blackHeight (Node _ _ h _ _ ) = h



balBST :: Node k v -> BalBST k v
balBST n@(Leaf _) = BalBST n
balBST n          = BalBST . blacken $ n

blacken :: Node k v -> Node k v
blacken (Node c l h k r) = let h' = if c == Black then h else h + 1
                           in Node Black l h' k r


empty :: BalBST k v
empty = Empty


--foo :: [a] -> a

singleton :: v -> BalBST k v
singleton x = BalBST (Leaf x)

--------------------------------------------------------------------------------


member :: (k `IsKeyFor` v, Ord k, Eq v) => v -> BalBST k v -> Bool
member _ Empty = False
member x (BalBST n) = memberN x n

memberN :: (Ord k, Eq v, k `IsKeyFor` v) => v -> Node k v -> Bool
memberN x (Leaf v) = x == v
memberN x (Node _ l _ k r) = let t = if goLeft x k then l else r
                            in memberN x t



--------------------------------------------------------------------------------

-- pre: max left <= min right

join :: (k `IsKeyFor` v) => BalBST k v -> BalBST k v -> BalBST k v
Empty        `join` r = r
l@(BalBST _) `join` Empty = l
(BalBST l)   `join` (BalBST r) = balBST $ l `joinN` r

joinN :: (k `IsKeyFor` v) => Node k v -> Node k v -> Node k v
l `joinN` r
  | blackHeight l <= blackHeight r = joinNodeR l r
  | otherwise                      = joinNodeL l r



-- pre: - blackHeight Left >= blackHeight Right
--      - max left <= min right

joinNodeL :: (k `IsKeyFor` v) => Node k v -> Node k v -> Node k v
joinNodeL l@(Leaf _) r           = balance Red   l  0 r
  -- if l is a leaf, the blackheight of r must be 0 as well, and thus we attach here
joinNodeL l@(Node Black lc  h _ rc) r
  | h == blackHeight r           = balance Red   l  h r
  | otherwise                    = balance Black lc h (joinNodeL rc r)
joinNodeL (Node Red lc h _ rc) r = balance Red   lc h (joinNodeL rc r)

-- pre: - blackHeight Left <= blackHeight Right
--      - max left <= min right

joinNodeR :: (k `IsKeyFor` v) => Node k v -> Node k v -> Node k v
joinNodeR l r@(Leaf _)             = balance Red   l 0 r
  -- if l is a leaf, the blackheight of r must be 0 as well, and thus we attach here
joinNodeR l r@(Node Black lc  h _ rc)
  | h == blackHeight l           = balance Red   l  h r
  | otherwise                    = balance Black (joinNodeR l lc) h rc
joinNodeR l (Node Red lc h _ rc) = balance Red   (joinNodeR l lc) h rc





balance :: (k `IsKeyFor` v) => Color -> Node k v -> BlackHeight -> Node k v -> Node k v
balance Black (Node Red (Node Red a _ _ b) _ _ c) h d = bal h a b c d
balance Black (Node Red a _ _ (Node Red b _ _ c)) h d = bal h a b c d

balance Black a h (Node Red b _ _ (Node Red c _ _ d)) = bal h a b c d
balance Black a h (Node Red (Node Red b _ _ c) _ _ d) = bal h a b c d
balance c     l h r                                   = node c l h r


bal :: (k `IsKeyFor` v)
       => BlackHeight -> Node k v -> Node k v -> Node k v -> Node k v -> Node k v
bal h a b c d = node Red (node Black a h b) h (node Black c h d)


node :: (k `IsKeyFor` v) => Color -> Node k v -> BlackHeight -> Node k v -> Node k v
node c l h r = Node c l h (l <..> r) r
  where
    (Leaf x)         <..> (Leaf y)         = toKey x <> toKey y
    (Leaf x)         <..> (Node _ _ _ k _) = toKey x <> k
    (Node _ _ _ k _) <..> (Leaf x)         = k <> toKey x
    (Node _ _ _ k _) <..> (Node _ _ _ z _) = k <> z




--------------------------------------------------------------------------------




-- pre: x \in tree

-- Given a tree t with elements v_1,..,v_k,x,v_{k+2},..,v_n into a tree for
-- v_1,..,v_k, the element x, and a tree for elements v_{k+2}, v_n.

split :: (k `IsKeyFor` v) => v -> BalBST k v -> (BalBST k v, v, BalBST k v)
split _ Empty = error "split: on empty tree"
split x (BalBST n) = splitNode x n

-- More specifically. SplitNode finds the leaf y that searching for x guides us
-- to, and returns this y.

splitNode :: (k `IsKeyFor` v) => v -> Node k v -> (BalBST k v, v, BalBST k v)
splitNode _ (Leaf y) = (Empty, y, Empty)
splitNode x (Node _ l _ k r)
  | goLeft x k = let (l',m,r') = splitNode x l in (l', m, r' `join` BalBST r)
  | otherwise  = let (l',m,r') = splitNode x r in (BalBST l `join` l', m, r')





delete :: (Eq v, k `IsKeyFor` v) => v -> BalBST k v -> BalBST k v
delete x t = let (l,y,r) = split x t in
             if x == y then l `join` r else t

deleteUnSafe     :: (k `IsKeyFor` v) => v -> BalBST k v -> BalBST k v
deleteUnSafe x t = let (l,_,r) = split x t in l `join` r


insert :: IsKeyFor k v => v -> BalBST k v -> BalBST k v
insert x t = l `join` m `join` r
  where
    (l,y,r) = split x t
    m       = if goLeft x (toKey x <> toKey y) then singleton x `join` singleton y
                                               else singleton y `join` singleton x



sing :: a -> BalBST (Key a) (Id a)
sing = singleton . Id




--------------------------------------------------------------------------------

data Range a = Range a a
               deriving (Show,Read,Eq,Ord)

data Key a = Key a a
                deriving (Show,Eq,Ord)

instance Semigroup (Key a) where
  (Key _ ml) <> (Key _ mr) = Key ml mr

newtype Id a = Id a deriving (Show,Eq,Ord)

instance Ord a => (Key a) `IsKeyFor` (Id a) where
  toKey (Id x) = Key x x

  goLeft (Id x) (Key y _) = x <= y

--------------------------------------------------------------------------------

fromSortedList :: (k `IsKeyFor` v) => [v] -> BalBST k v
fromSortedList = foldr (\x t -> singleton x `join` t) Empty

singN = Leaf . Id

n1 = singN 1
n2 = singN 2
n10 = singN 10
n20 = singN 20

t1 = n1 `joinN` n2
t2 = n10 `joinN` n20
