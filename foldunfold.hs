-- http://blog.ezyang.com/2012/10/duality-for-haskellers/
-- https://kseo.github.io/posts/2016-12-12-unfold-and-fold.html

{-# OPTIONS -XStandaloneDeriving -XFlexibleContexts -XUndecidableInstances #-}

import Prelude hiding(foldr, sum, length, fmap, Functor)


{-

Study the eelationship between fold, unfold, and Mu using category theory.

-}

--Consider this recursive foldr operating on recursive data type List

data List a = Cons a (List a) | Nil deriving Show
-- notice Cons is a constructor that takes two parameters: one of type 'a' and another of type 'List a'.

foldr :: (a -> r -> r) -> r -> List a -> r
foldr f i Nil = i
foldr f i (Cons x xs) = f x (foldr f i xs)

-- sample usage

sum :: List Int -> Int
sum = foldr (\e c -> e + c) 0 

l1 = Cons 10 (Cons 9 (Cons 8 (Cons 7 (Cons 6 (Cons 5 (Cons 4 (Cons 3 (Cons 2 (Cons 1 Nil)))))))))

test1 = foldr (\e c -> e + c) 0 l1

{-

If you look at above foldr, it takes 3 arguments: (a -> r -> r),  r, List a. 
Except for  the last/list arg, the remaining do not have a good representation in category theory.

What we could do is create another function that takes categorical product (pair or comma or any bifunctor) of 'a' and 'r' as a single argument.
And we change fold to take this function itself as argument and returns combined 'r'.
Also we need to take care of the situation where List can be empty: i.e., we could not pass in 'a', but expect the reduction/folding just return (initial) 'r'.

To prove that there is an isomorphism between the two, see this: https://kseo.github.io/posts/2016-12-12-unfold-and-fold.html

-}

-- First try using a built-in functor, Comma to shove in the two arguments. But Since we also need to account for empty list case, use Mabe with it.


gM :: Maybe (Int, Int) -> Int
gM (Just (x, xs)) = (\e c -> e + c) x xs
gM Nothing = 0

-- Notice, that since the function gM, that reduces two values into one is specific to type of values being folded, it is not a generic function (i.e., does not use type parameters)

-- Now the new fold that takes the Functor in the input

foldM :: (Maybe (a, r) -> r) -> List a -> r
foldM g Nil = g Nothing  --- has to return the initial r
foldM g (Cons x xs) = g (Just (x, (foldM g xs)))

test2 = foldM gM l1

-- Instead of using Maybe and Comma together, can we concact our own and use it so that we have control on how it is defined.
data ListF a r = ConsF a r | NilF deriving (Show, Eq)

-- F in List"F" in the end stands for Functor


gF :: ListF Int Int -> Int
gF (ConsF x xs) = (\a r -> a + r) x xs
gF NilF = 0

foldF :: (ListF a r -> r) -> List a -> r
foldF g Nil = g NilF
foldF g (Cons x xs) = g (ConsF x (foldF g xs))

test3 = foldF gF l1

-- Note that we addressed only mapping object part of a functor (Int -> ListF Int Int)
-- What do we have now ?

{-

                             ListF a R
                                |
                                |
                                g
                                |
                                |
                                v
    List a ------fold g ------> R

-}

-- It would be nice if we can complete a square or triangle and make it commute as that is what we usullay look for when categorical analysis on a problem.
-- For it we need to somehow relate 'List a' to 'ListF a R' !

-- Convert  List to ListF by storing List a as r of ListF a r. What is stored for 'a'? may be pass the first element of List while r stores rest of n-1 elements?


inx :: ListF a (List a) -> List a
inx (ConsF x xs) = Cons x xs       -- notice, the whole 'List a' instance is in xs, not individually broken down by (ConsF a (ConsF b ....))
inx NilF = Nil


{-

   ListF a (List a) ----   ?   ----> ListF a R   (R stores result of folding/reducing)
      |                                   |
      |                                   |
     inx                                  g
      |                                   |
      |                                   |
      v                                   v
    List a -----------fold g -----------> R

-}

-- Note that so far we used ListF as a type that takes a type argument to create a concrete type (type constructor) and not as a real functor as
-- we have not yet defined or used fmap for it.

-- Now we need to convert ListF (List a) to List a R
--- first make ListF, functorial (by implementing fmap)

{-
consider an f that converts 'List a' to R (if non-null list, reduces all + initial value else just initial value)
f :: List a -> r
then,
(fmap f):: ListF a (List a) -> ListF a r
-}

class Functor f where
  fmap :: (a -> b) -> f a -> f b

instance Functor (ListF a) where
  fmap f NilF = NilF
  fmap f (ConsF x xs) = ConsF x (f xs)   -- notice f is applied to xs leaving x alone as it corresponds to 'a' of 'ListF a r' and 'r' is the type parameter of the functor

-- just a helper
out g = fmap (foldF g)

{-

   ListF a (List a) ---- fmap (fold g) -----> ListF a R   (R stores result of folding)
      |                                           |
      |                                           |
     in                                           g
      |                                           |
      |                                           |
      v                                           v
    List a -------------- fold g ---------------> R


Notice that the diagram must commute! (That is to say, fold g . inx == g . fmap (fold g)).  Otherwise inx is not unique, for example an alternative:

in NilF = Nil
in (ConsF a as) = Cons a $ Cons a as
also has type ListF a (List a) -> List a, and so do
in NilF = Nil
in (ConsF a as) = case as of Nil -> Nil ; (Cons b bs) -> Cons a $ Cons b Nil  -- notice the throwing away of bs!

Above non-uniqueness example is given as a comment in http://blog.ezyang.com/2012/10/duality-for-haskellers/.


Also, notice that currently foldF is not parametric in the functor parameter, but hard coded for ListF only.

-}

{-
Look at  these two:
   data ListF a r = ConsF a r        | NilF deriving Show
   data List  a   = Cons  a (List a) | Nil deriving Show

Using Mu, ListF a  can be converted into List a !
instance Show (Mu f) where
  show (In v) = "In " ++ (show v)
-}

data Mu f = In (f (Mu f))

-- type ListX a = Mu (ListF a)

nilf = In NilF
consf x xs = In (ConsF x xs)

{-

   (ListF a) (Mu (ListF a)) ---- fmap (fold g) -----> ListF a R   (R stores result of folding)
      |                                                   |
      |                                                   |
     in                                                   g
      |                                                   |
      |                                                   |
      v                                                   v
    (Mu ListF a) ---------------- fold g ---------------> R


With the help of Mu, and using 'g . fmap (fold g)' path, now we can write foldF generically in the functor parameter:

So, instead of
foldF :: (ListF a r -> r) -> List a -> r
foldF g Nil = g NilF
foldF g (Cons x xs) = g (ConsF x (foldF g xs))

we could do this:

-}

foldFG :: (Functor f) => (f r -> r) -> Mu f -> r
foldFG g (In x)  = g ( fmap (foldFG g) x)

{-
     F (Mu F) ---- F (fold g) -----> F X 
      |                               |
      |                               |
     in                               g
      |                               |
      |                               |
      v                               v
     Mu F -------- fold g ----------> X

because 

A beneficial side-effect of separating out the recursion in the
datatype from the shape, is that a program that depends only on the
recursive nature of a datatype and can be parametrised by the shape
can be written once and for all, as a datatype-generic function.

-}

{-

Now for the dual of fold by reversing all arrows:


   (ListF a) (Mu (ListF a)) <--- fmap (fold g) ------ ListF a R   (R stores result of folding)
     /\                                                  /\
      |                                                   |
     in                                                   g
      |                                                   |
      |                                                   |
      |          /                                        |
    (Mu ListF a) \--------------- fold g ---------------- R
                
Or 
     
      R --------------- unfold f ----------------> (Mu ListF a)
      |                                                   |
      |                                                   |
      f                                                 outx
      |                                                   |
      |                                                   |
      v                                                   v
 ListF a R -------- fmap (unfold f) ----------> (ListF a) (Mu (ListF a)) 


--foldF :: (ListF a r -> r) -> List a -> r   (reverse all arrows)
unfoldr :: (b -> Maybe (a, b)) -> (b -> [a])
unfoldr :: (r -> ListF a r) -> (r -> List a)

inx (ConsF x xs) = Cons x xs       -- notice, the whole 'List a' instance is in xs, not individually broken down by (ConsF a (ConsF b ....))
-}


outx x = ConsF 0 x

f :: Int -> ListF Int Int
f 0 = NilF
f v = ConsF v (v-1)

unfoldF :: (r -> ListF a r) -> r -> Mu (ListF a)
unfoldF f v = case f v of
              ConsF x xs -> consf x (unfoldF f xs)
              NilF -> nilf

ulhs = outx . (unfoldF f)
urhs = fmap (unfoldF f) . f

{-
We could also use bifunctor as below.

Earlier, we parametrized Mu on the shape (recursive position) parameter only, not on the container element type (only on 'r' of ListF a r for example and not on 'a')

data Mu f = In (f (Mu f))

We could abstract over element type and shape (or type of recrusive position) parameter using bifunctor:

-}

class Bifunctor f where
  bimap :: (a->c) -> (b->d) -> f a b -> f c d


{-
With:
  bimap id id = id
  bimap f g . bimap h j = bimap (f . h) (g . j)

So,
-}

data MuB bif a = InB { inb_ :: bif a (MuB bif a) }

foldB :: Bifunctor f => (f a b -> b) -> MuB f a -> b
foldB g (InB x) = g (bimap id (foldB g) x)

instance Bifunctor ListF where
  bimap f g NilF  = NilF
  bimap f g (ConsF x xs) = ConsF (f x) (g xs)

-- an example

length :: MuB ListF a -> Int
length = foldB gB where
  gB NilF = 0
  gB (ConsF a b) = 1+b

nilbf = InB NilF
consbf x xs = InB (ConsF x xs)

testln = do
  print $ length (consbf "c" (consbf "a" (consbf "b" nilbf)))

-- see bottom of http://www.prg.nii.ac.jp/course/2013/springCourse/source/lecture1.lhs for more deriving like below
deriving instance Show (f (Mu f)) => Show (Mu f)

lf = consf 10 (consf 9 (consf 8 (consf 7 (consf 6 (consf 5 (consf 4 (consf 3 (consf 2 (consf 1 nilf)))))))))

main = do
  print $ test1
  print $ test2
  print $ test3
  print "--- fold ----"
  print $ inx (ConsF 0 l1)   -- notice storing  of initial value, 0  in ConsF 0 ...
  print $ out gF (ConsF (0::Int) l1)
  print $ gF (out gF (ConsF (0::Int) l1))
  print $ (foldF gF) (inx (ConsF (0::Int) l1))
  print "--- fold generic ----"
  print $ foldFG gF lf
  print "--- unfold ----"
  print $ f (10::Int)
  print $ ulhs (10::Int)
  print $ urhs (10::Int)
  -- before equating, we need to implement Eq for Mu
  -- print $ ulhs (10::Int) == urhs (10::Int)
  print "--- bifunctor based ----"
  testln
