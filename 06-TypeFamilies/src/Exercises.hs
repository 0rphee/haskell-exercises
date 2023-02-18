{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Exercises () where

import Data.Kind (Constraint, Type)

-- | Before we get started, let's talk about the @TypeOperators@ extension. All
-- this does is allow us to write types whose names are operators, and write
-- regular names as infix names with the backticks, as we would at the value
-- level.





{- ONE -}

data Nat = Z | S Nat

-- | a. Use the @TypeOperators@ extension to rewrite the 'Add' family with the
-- name '+':

type family (leftVal :: Nat) + (rightVal :: Nat) :: Nat where
  Z + xs = xs
  S xs + ys = S (xs + ys)


-- | b. Write a type family '**' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why?

type family (lval :: Nat) ** (rval :: Nat) :: Nat where
  Z ** any = Z
  S xs ** ys = ys + (xs ** ys)


data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | c. Write a function to add two 'SNat' values.

addition :: SNat a -> SNat b -> SNat (a + b)
addition SZ x = x
addition (SS xs) ys = SS (addition xs ys)




{- TWO -}

data Vector (count :: Nat) (a :: Type) where
  VNil  :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | a. Write a function that appends two vectors together. What would the size
-- of the result be?

append :: Vector m a -> Vector n a -> Vector (m + n) a
append VNil xs = xs
append (VCons x xs) ys = VCons x (append xs ys)

-- | b. Write a 'flatMap' function that takes a @Vector n a@, and a function
-- @a -> Vector m b@, and produces a list that is the concatenation of these
-- results. This could end up being a deceptively big job.

flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n ** m) b
flatMap VNil _ = VNil
flatMap (VCons x xs) f = f x `append` flatMap xs f





{- THREE -}

-- | a. More boolean fun! Write the type-level @&&@ function for booleans.
type family (lb :: Bool) && (lr :: Bool) :: Bool where
  False && _ = False
  True && n = n

-- | b. Write the type-level @||@ function for booleans.

type family (lb :: Bool) || (lr :: Bool) :: Bool where
  False || n = n
  True || _ = True


-- | c. Write an 'All' function that returns @'True@ if all the values in a
-- type-level list of boleans are @'True@.
type family All (lb :: [Bool]) :: Bool where
  All '[] = True
  All (x:xs) = x && All xs


{- FOUR -}

-- | a. Nat fun! Write a type-level 'compare' function using the promoted
-- 'Ordering' type.

type family Compare (l :: Nat) (r :: Nat) :: Ordering where
  Compare Z Z     = EQ
  Compare Z (S n) = LT
  Compare (S xs) (S ys) = Compare xs ys


-- | b. Write a 'Max' family to get the maximum of two natural numbers.
type family Max (l :: Nat) (r :: Nat) :: Nat where
  Max xs ys = IfM (Compare xs ys) xs ys 

type family IfM (ord :: Ordering) (l :: Nat) (r :: Nat) :: Nat where
  IfM LT _ y = y
  IfM _  x _ = x

-- | c. Write a family to get the maximum natural in a list.
type family MaxInList (list :: [Nat]) :: Nat where
  MaxInList '[] = Z
  MaxInList (x:xs) = Max x (MaxInList xs)





{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.
type family InsertNat (nat :: Nat) (tree :: Tree) :: Tree where
  InsertNat nat Empty = Node Empty nat Empty
  InsertNat nat (Node lt c rt) = IfI (Compare nat c) nat (Node lt c rt)

type family IfI (ord :: Ordering) (l :: Nat) (r :: Tree) :: Tree where
  IfI LT x (Node lt c rt) = Node (InsertNat x lt) c rt
  IfI GT x (Node lt c rt) = Node lt c (InsertNat x rt) 
  IfI _  _ xs = xs





{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
-- type family Dnat (nat :: Nat) (tree :: Tree) :: Tree where
--   Dnat _ Empty = Empty
--   Dnat x (Node l c r) = 

-- type family DD (Compare )





{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.

data HList (xs :: [Type]) where
  HNil  :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)


type family (l :: [Type]) ++ (r :: [Type]) :: [Type] where
  '[] ++ xs = xs
  (x:xs) ++ ys = x : (xs ++ ys)


-- | Write a function that appends two 'HList's.

appendH :: HList a -> HList b -> HList (a ++ b)
appendH HNil xs = xs
appendH (HCons x xs) ys = HCons x (appendH xs ys) 




{- EIGHT -}

-- | Type families can also be used to build up constraints. There are, at this
-- point, a couple things that are worth mentioning about constraints:
--
-- - As we saw before, '()' is the empty constraint, which simply has "no
--   effect", and is trivially solved.
--
-- - Unlike tuples, constraints are "auto-flattened": ((a, b), (c, (d, ())) is
--   exactly equivalent to (a, b, c, d). Thanks to this property, we can build
--   up constraints using type families!

type family CAppend (x :: Constraint) (y :: Constraint) :: Constraint where
  CAppend x y = (x, y)

-- | a. Write a family that takes a constraint constructor, and a type-level
-- list of types, and builds a constraint on all the types.

type family Every (c :: Type -> Constraint) (x :: [Type]) :: Constraint where
  Every c '[] = ()
  Every c (x:xs) = (c x, Every c xs)

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.
instance Every Show xs => Show (HList xs) where
  show HNil = "[]"
  show (HCons x xs) = show x ++ " : " ++ show xs

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?
instance Every Eq xs => Eq (HList xs) where
  (HCons x xs) == (HCons y ys) = x == y && xs == ys
  _ == _ = True

instance (Every Eq xs, Every Ord xs) => Ord (HList xs) where
  compare (HCons x xs) (HCons y ys) = compare x y <> compare xs ys
  compare _            _            = EQ




{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.

-- | b. Write a type-level prime number sieve.

-- | c. Why is this such hard work?
