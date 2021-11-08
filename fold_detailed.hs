{-# OPTIONS -XFlexibleInstances -XStandaloneDeriving #-}

-- In the whole discussion below, ListR and ListX are the critical to understand.

import Prelude hiding(map, sum, Functor, fmap)

class Functor f where
  fmap :: (a->b) -> f a -> f b

data List a = Cons a (List a) | Nil deriving Show
fold1 :: b -> (a -> b -> b) -> List a -> b
fold1 e g Nil = e
fold1 e g (Cons a xs) = g a (fold1 e g xs)

sum1 a b = a + b

list1 = (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil)))))

test1 = do
  print $  fold1 0 sum1 list1

-- how do we make fold recurse without knowing the shape of List? use type constructor


data Holder f a e = Holder (f a) e Bool deriving Show
-- notice 'e' after 'f a' rather than other way around, it helps later in converting Holder into functor
-- Bool field at the end is used as an indication to fold if recrusion should be terminated.
 
fold2 :: b -> (b -> f a -> Holder f a b) -> f a -> b
fold2 e g m = if r then (fold2 ne g nm) else ne
  where Holder nm ne r = g e m

sum2:: Int -> List Int -> Holder List Int Int
sum2 e (Cons i xs) = Holder xs (e+i) True
sum2 e Nil = Holder Nil e False

test2 = fold2 10 sum2 list1

runtest2 = do
  print test2

{-

-- Instead of using a boolean variable to tell fold to recurse or not:
-- since f is type constructor above, we could make it implement fmap and let it decide
-- to apply '(fold2 ne g nm)' further or not based on (current) shape value Cons vs. Nil.
-}


-- sum2 is doing 2 things: summing two elements; recursing based on shape... let's see if we can seprate
-- responsibilities

step :: (Holder List a b -> b) -> b -> List a -> Holder List a b
step s e (Cons i xs) = Holder xs (s (Holder (Cons i xs) e False) ) True
step s e Nil = Holder Nil (s (Holder Nil e False) ) False

{-
Idea of step is that fold and step recurse back and forth (mutual recursion) to remove one element at a time from the right and create a new initial value

[1,2,3,4,5], 0
[1,2,3,4], 5
[1,2,3], 9

and so on...
-}

sum3 :: Holder List Int Int -> Int
sum3 (Holder (Cons a xs) e _)  = a + e
sum3 (Holder Nil e _) = e

test3  = fold2 10 (step sum3) list1

runtest3 = do
  print test3

len3:: Holder List Int Int -> Int
len3 (Holder (Cons a xs) e _) = 1 + e
len3 (Holder Nil e _) = e

test4  = fold2 0 (step len3) list1

runtest4 = do
  print test4

-- the functions like sum3, len3 already know what the initial values are, they need not be told. Let's fix it.
-- also Holder is now holding data for two different reasons: recurse or not; current state (current rolled up value; remaining (list) items. let's separate them too.

data Cursor f a e = Cursor (f a) e deriving Show

fold3 :: (f a -> Cursor f a b) -> f a -> b
fold3 g m = ne
  where Cursor nm ne = g m

data Data f a b = Data1 (f a) b | NilD deriving Show

step2 :: (Data List a b -> b) -> List a -> Cursor List a b
step2 s (Cons i xs) = Cursor xs rolled
  where inner = fold3 (step2 s) xs
        rolled = s (Data1 (Cons i Nil) inner )
step2 s Nil = Cursor Nil rolled
  where rolled = s NilD

-- step uses cursor to send info up to fold; step uses data to send info down to sum

sum4 :: Data List Int Int -> Int
sum4 (Data1 (Cons a xs) e )  = a + e   -- information (xs) leakage
sum4 NilD = 0

test5  = fold3 (step2 sum4) list1

runtest5 = do
  print "Test 5"
  print test5

len4:: Data List Int Int -> Int
len4 (Data1 (Cons a xs) e ) = 1 + e  -- (1)
len4 NilD = 0

test6  = fold3 (step2 len4) list1

runtest6 = do
  print "Test 6"
  print test6

-- Cursor does not seem to be useful after all. Let's remove it.

fold4 :: (f a -> b) -> f a -> b
fold4 g m = g m

step3 :: (Data List a b -> b) -> List a -> b
step3 s (Cons i xs) = rolled
  where inner = fold4 (step3 s) xs
        rolled = s (Data1 (Cons i Nil) inner )
step3 s Nil = s NilD

-- Alas, we now made step do two things just like fold used to do!

test7  = fold4 (step3 sum4) list1

runtest7 = do
  print "Test 7"
  print test7

test8  = fold4 (step3 len4) list1

runtest8 = do
  print "Test 8"
  print test8

{-

Why bother client of fold to know about existence of step function.
We could delegate that work to type being folded (List). It will implement a well defined interface and fold internally adds step based on knowing that the 'folded' implements it.
-}

fold5 :: Whatever f => (Data f a b -> b) -> f a -> b
fold5 g m = (stepr g) m

class Whatever f where
  stepr :: (Data f a b -> b) -> f a -> b

instance Whatever List where
  stepr s (Cons i xs) = rolled
    where inner = fold5 s xs
          rolled = s (Data1 (Cons i Nil) inner )  -- (2)
  stepr s Nil = s NilD

test9  = fold5 sum4 list1

runtest9 = do
  print "Test 9"
  print test9

test10  = fold5 len4 list1

runtest10 = do
  print "Test 10"
  print test10

{-
In (1) step always passes Nil for xs; Also, by this time step  already calculated the rolled up value of xs.

In (2)  notice I am passing Nil for xs; Also the folding function does not use it (otherwise it will see Nil which is bad). Also by this time roll up is calculated for xs!

So, can we reuse this field by converting into a type parameter?

-}

data ListR a b = ConsR a (ListR a b) | ConsE a b | NilR deriving Show

{-

Here the type parameter we were talking about is the second parameter 'b':

Below:
'e' represents the rolled up value type when 'b' of 'ListR a b' is instantiated for it.
'r' represents the recursion type when 'b' of 'ListR a b' inistantiated for it.
-}

fold6 :: Whatever2 f => (f a e -> e) -> f a r -> e
fold6 g m = (stepr2 g) m

class Whatever2 f where
  stepr2 :: (f a e -> e) -> (f a r -> e)

instance Whatever2 ListR where

  stepr2 s NilR = s NilR

  stepr2 s (ConsR i xs) = rolled
    where inner = fold6 s xs
          rolled = s (ConsE i inner)

sum5 :: ListR Int Int -> Int
sum5 NilR = 0
sum5 (ConsE a e)  = a + e

list2 = (ConsR 1 (ConsR 2 (ConsR 3 (ConsR 4 (ConsR 5 NilR)))))
test11  = fold6 sum5 list2

runtest11 = do
  print "Test 11"
  print test11

len5:: ListR Int Int -> Int
len5 (ConsE a e) = 1 + e
len5 NilR = 0

test12  = fold6 len5 list2

runtest12 = do
  print "Test 12"
  print test12

-- Whatever has nothing to do with folding function, why pass through it... let's fix it.

class Whatever3 f where
  stepr3 :: (f a r -> e) -> (f a r -> f a e)

fold7 :: Whatever3 f => (f a e -> e) -> f a r -> e
fold7 g m = g ( stepr3 (fold7 g) m )

instance Whatever3 ListR where
  stepr3 f NilR = NilR
  stepr3 f (ConsR i xs) = ConsE i (f xs)

test13  = fold7 sum5 list2

runtest13 = do
  print "Test 13"
  print test13

test14  = fold7 len5 list2

runtest14 = do
  print "Test 14"
  print test14

{-
Let's look at ListR again:
data ListR a b = ConsR a (ListR a b) | ConsE a b | NilR deriving Show

All good except that ListR is ugly: bunch of concepts crammed in one, in particular 2 constructors for two different concepts (recursion, storing partial results).

Could we fix it?
We should make it more generic:
data ListF a b = ConsF a b | NilF deriving Show

Represent recursion by instantiating b as 'ListF a' ad infinitum but then break by terminal condition:

 
Also whatever3 is almost like a functor, but not convertable to one yet.

-}

data ListF a b = ConsF a b | NilF deriving Show

-- instantiate 'b' in ListF with self to handle recursion
data ListX a = InX (ListF a (ListX a))   
-- InX because data needs a constructor name;
-- Also, you cannot do recursion with pure type aliasing 'type ListX a = ListF a (ListX a)' is not allowed
-- so you cannot avoid using data.

list3::ListX Int
list3 = InX (ConsF 3 (InX (ConsF 4 (InX (ConsF 5 (InX NilF))))))

class Whatever4 f where
  stepr4 :: (x -> y) -> (f a x -> f a y)

instance Whatever4 ListF where
  stepr4 f NilF = NilF
  stepr4 f (ConsF i xs) = ConsF i (f xs)

--handles ListX / recursion aspect
fold8 :: (ListF a e -> e) -> ListX a -> e
fold8 g (InX m) = g ( stepr4 (fold8 g) m )

sum6 :: ListF Int Int -> Int
sum6 NilF = 0
sum6 (ConsF a e)  = a + e

test15  = fold8 sum6 list3

runtest15 = do
  print "Test 15"
  print test15

len6:: ListF Int Int -> Int
len6 (ConsF a e) = 1 + e
len6 NilF = 0

test16  = fold8 len6 list3

runtest16 = do
  print "Test 16"
  print test16


-- But, I do not think we have this in mind for fold(8). It is hard coded to work for List only although now recursion is seprated from shape

-- We need to abstract ListX that allows to abstract ListF in fold8 definition...

data Mu f a = In (f a (Mu f a))
type ListY a = Mu ListF a

fold9 :: Whatever4 f => (f a e -> e) -> Mu f a -> e
fold9 g (In m) = g ( stepr4 (fold9 g) m )

list4::ListY Int
list4 = In (ConsF 3 (In (ConsF 4 (In (ConsF 5 (In NilF))))))

test17  = fold9 sum6 list4

runtest17 = do
  print "Test 17"
  print test17

test18  = fold9 len6 list4

runtest18 = do
  print "Test 18"
  print test18

-- Now, we can also change Whatever4 to Functor, noting that that Finctor takes  only 1 type argument
fold10 :: Functor (f a) => (f a e -> e) -> Mu f a -> e
fold10 g (In m) = g ( fmap (fold10 g) m )

instance Functor (ListF a) where
  fmap f NilF = NilF
  fmap f (ConsF i xs) = ConsF i (f xs)

test19  = fold10 sum6 list4

runtest19 = do
  print "Test 19"
  print test19

test20  = fold10 len6 list4

runtest20 = do
  print "Test 20"
  print test20

-- Now you can convert ListF into bi-functor to enable map etc., on it...

class Bifunctor f where
  bimap :: (a->b) -> (c->d) -> (f a c -> f b d)

instance Bifunctor ListF where
  bimap f1 f2 NilF = NilF
  bimap f1 f2 (ConsF i a) = ConsF (f1 i) (f2 a)    --- (3)

fold11 :: Bifunctor f => (f a e -> e) -> Mu f a -> e
fold11 g (In m) = g ( bimap id (fold11 g) m )

test21  = fold11 sum6 list4

runtest21 = do
  print "Test 21"
  print test21

test22  = fold11 len6 list4

runtest22 = do
  print "Test 22"
  print test22

-- As container, List still maintains its 'map' feature...

map :: Bifunctor f => (a -> b) -> Mu f a -> Mu f b
map f (In x)  = In (bimap f (map f) x)   -- see eqn (3)

test23 = fold11 sum6 (map (\x -> x + 1) list4)

runtest23 = do
  print "Test 23"
  print test23

-- How'bout unfold?

unfold :: Bifunctor f => (b -> f a b) -> f a b -> Mu f a
unfold f (In x) = bimap id (unfold f) x 

{-
range m n = unfold next
  where next = if (m == n)
                 NilF
               else
                 ConsF m (m+1, n)
-}

-- main

main = do
  test1
  runtest2
  runtest3
  runtest4
  runtest5
  runtest6
  runtest7
  runtest8
  runtest9
  runtest10
  runtest11
  runtest12
  runtest13
  runtest14
  runtest15
  runtest16
  runtest17
  runtest18
  runtest19
  runtest20
  runtest21
  runtest22
  runtest23

