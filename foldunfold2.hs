{-# OPTIONS -XStandaloneDeriving -XFlexibleContexts -XUndecidableInstances #-}


import Prelude hiding(sum, Functor, fmap, map, length)

data List a = Cons a (List a) | Nil

fold :: b -> (b -> f a -> b)  -> f a -> b
fold e g m  = g e m

listsummer :: Integer -> List Integer -> Integer
listsummer e (Cons a xs) = a + (fold e listsummer xs)
listsummer e Nil = e

listsum = fold 0 listsummer

test1 = do
  print $  listsum (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil)))))

data BinTree a = NilT | Node a (BinTree a) (BinTree a)
treesummer :: Integer -> BinTree Integer -> Integer
treesummer e NilT = e
treesummer e (Node a l r ) = a + (fold e treesummer l) + (fold e treesummer r)

treesum = fold 0 treesummer

node v = Node v NilT NilT

test2 = do
  print $ treesum (Node 10 (node 20) (Node 30 (node 40) (node 50)))

-- Usually each folding function like listsummer, treesummer know the initial values and all fold doing is being a pass through of the initial value, e; fold does not need it ... bad coupling... can it be fixed ?

fold':: (f a -> b) -> f a -> b
fold' g m = g m

listsummer' :: List Integer -> Integer
listsummer' (Cons a xs) = a + (fold' listsummer' xs)
listsummer' Nil = 0

listsum' = fold' listsummer'

test3 = do
  print $  listsum' (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil)))))

{-
All we did with ' stuff is move walking of recursion to folding function forcing each to implement it ! We actually converted into mutual recursion between folding function and fold itself.

What do we do now? we do not want fold to know the shape, and we do not want folding function to know recursion. 

We want to separate responsibilities so that only fold knows about recursion and only folding function knows about shape, initial value, and folding operation


In listsummer' (Cons a xs)  if 'xs' is the folded answer so far, it will simplify to 
listsummer' (Cons a xs)  = a + xs 
And it will be awesome.

So, We want something like:

ListF a b = Cons a b
Here b is result type. I.e, instantiate as 'a =  Int, b = Int'.

And Likewise

ListF a <what?> = List a

Since our datatype is recursive as:

List a = Cons x (List a)

ListF a (ListF a) could  be used for recursive data type! i.e, instantiate as 'a = Int , b = (ListF Int)'.

We can further simplify with 
data Mu1 f = In1 (f (Mu1 f))

-}
data Mu1 f = In1 (f (Mu1 f))
data ListF a b = ConsF a b | NilF

type List' a = Mu1 (ListF a)

--listsummer'' :: ListF Integer Integer -> Integer
listsummer'' (ConsF a xs) = a + xs
listsummer'' NilF = 0

-- now the functor would be List a, with b as type parameter.

class Functor f where
  fmap :: (a->b) -> (f a -> f b)

fold'' :: Functor f => (f b -> b) -> Mu1 f -> b
fold'' g (In1 x) = g (fmap (fold'' g ) x)

instance Functor (ListF a) where
  fmap f NilF = NilF
  fmap f (ConsF i a)  = ConsF i (f a)


icons v x = In1 (ConsF v x)

listsum'' = fold'' listsummer''

test4 = do
  print $  listsum''  (icons 1 (icons 2 (icons 3 (icons 4 (icons 5 (In1 NilF))))))

{-

Happy now?

Not completely.... 

Why? since List'  is just a type synonym, we cannot define Functor on List' directly.
And Mu1 (ListF a) is not a type constructor to define Functor for it.

instance Functor (Mu1 (ListF a)) where
  fmap f (In1 x) = In1 x

So, how do I map over list elements ?

Make it bifunctor!

-}

data Mu2 f a = In2 (f a (Mu2 f a))
class Bifunctor f where
  bimap :: (a->b) -> (c->d) -> (f a c -> f b d)

fold''' :: Bifunctor f => (f a b -> b) -> Mu2 f a -> b
fold''' g (In2 x) = g (bimap id (fold''' g) x)

instance Bifunctor ListF where
  bimap f1 f2 NilF = NilF
  bimap f1 f2 (ConsF i a) = ConsF (f1 i) (f2 a)


length :: Mu2 ListF a -> Int
length = fold''' g where
  g NilF = 0
  g (ConsF a b) = 1+b

sum :: Mu2 ListF Integer -> Integer
sum = fold''' g where
  g NilF = 0
  g (ConsF a b) = a+b

icons2 v x = In2 (ConsF v x)

map :: Bifunctor s => (a->b) -> (Mu2 s a) -> (Mu2 s b)
map f (In2 x) = In2 (bimap f (map f) x)


test5 = do
  print $ sum (map (\x -> x + (100::Integer)) (icons2 1 (icons2 2 (icons2 3 (icons2 4 (icons2 5 (In2 NilF)))))))

{-

instance Bifunctor f => Functor (Mu2 f) where
  fmap f = fold''' (In2 . bimap f id)
-}


test6 = do
  print $ sum (fmap (\x -> x + (100::Integer)) (icons2 1 (icons2 2 (icons2 3 (icons2 4 (icons2 5 (In2 NilF)))))))

instance Bifunctor f => Functor (Mu2 f) where
  fmap f (In2 x) = In2 (bimap f (map f) x)

{-
Now that we are able to define map in 3 ways (essentially 2):

instance Bifunctor f => Functor (Mu2 f) where
  fmap f (In2 x) = In2 (bimap f (map f) x)

instance Bifunctor f => Functor (Mu2 f) where
  fmap f = fold''' (In2 . bimap f id)

map :: Bifunctor s => (a->b) -> (Mu2 s a) -> (Mu2 s b)
map f (In2 x) = In2 (bimap f (map f) x)


Happy now?

- how do I dualise it?

-}
data Nu2 f a = Out_ { out :: f a (Nu2 f a) }

unfold''' :: Bifunctor f => (b -> f a b) -> b -> Nu2 f a
unfold''' phi = Out_ . bimap id (unfold''' phi) . phi

instance Bifunctor f => Functor (Nu2 f) where
  fmap f = unfold''' (bimap f id . out)

type Colist a = Nu2 ListF a
range :: (Int,Int) -> Colist Int
range = unfold''' next where
  next (m,n) = if m==n then NilF else ConsF m (m+1,n)

test7 = do
  print $ range (1, 10)

test8 = do
  print $ range (1,0)

{-
- well, a couple of things nagging me, how do we know it all works?
- where is the theoretical backing for all this? Bifunctor coherence conditions proof?
-}

deriving instance Show (f (Mu1 f)) => Show (Mu1 f)
deriving instance Show (f a (Mu2 f a)) => Show (Mu2 f a)
deriving instance (Show a, Show b) => Show (ListF a b)
deriving instance Show (f a (Nu2 f a)) => Show (Nu2 f a)

main = do
  test1
  test2 
  test3 
  test4 
  test5 
  test6 
  test7 
  -- test8  -- will print forever
