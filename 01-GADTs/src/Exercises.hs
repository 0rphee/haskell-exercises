{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Exercises () where
import Data.Foldable





{- ONE -}

-- | Let's introduce a new class, 'Countable', and some instances to match.
class Countable a where
  count :: a -> Int

instance Countable Int  where count   = id
instance Countable [a]  where count   = length
instance Countable Bool where count x = if x then 1 else 0

-- | a. Build a GADT, 'CountableList', that can hold a list of 'Countable'
-- things.

data CountableList where
  CNil :: CountableList
  CCons :: Countable a => a -> CountableList -> CountableList
  -- ...


-- | b. Write a function that takes the sum of all members of a 'CountableList'
-- once they have been 'count'ed.

countList :: CountableList -> Int
countList CNil = 0
countList (CCons h t) = count h + countList t


-- | c. Write a function that removes all elements whose count is 0.

dropZero :: CountableList -> CountableList
dropZero CNil                       = CNil
dropZero (CCons h t) | count h == 0 = dropZero t
                     | otherwise    = CCons h $ dropZero t


-- | d. Can we write a function that removes all the things in the list of type
-- 'Int'? If not, why not?

filterInts :: CountableList -> CountableList
filterInts = error "Contemplate me!"





{- TWO -}

-- | a. Write a list that can take /any/ type, without any constraints.

data AnyList where
  ANil :: AnyList
  ACons :: a -> AnyList -> AnyList
  -- ...

-- | b. How many of the following functions can we implement for an 'AnyList'?

-- 1:2:3:4: []

reverseAnyList :: AnyList -> AnyList
reverseAnyList l = go l ANil
  where go :: AnyList -> AnyList -> AnyList
        go ANil carry = carry
        go (ACons h t) carry = go t (ACons h carry)

-- filterAnyList :: (a -> Bool) -> AnyList -> AnyList
-- filterAnyList f ANil = ANil 
-- filterAnyList f (ACons h t ) = if f h 
--                                then ACons h (filterAnyList f t)
--                                else filterAnyList f t



lengthAnyList :: AnyList -> Int
lengthAnyList ANil = 0
lengthAnyList (ACons _ t) = 1 + lengthAnyList t


-- foldAnyList :: Monoid m => AnyList -> m
-- foldAnyList = undefined

isEmptyAnyList :: AnyList -> Bool
isEmptyAnyList ANil = True
isEmptyAnyList _    = False

instance Show AnyList where
  show = error "What about me?"





{- THREE -}

-- | Consider the following GADT:

data TransformableTo output where
  TransformWith
    :: (input -> output)
    ->  input
    -> TransformableTo output

-- | ... and the following values of this GADT:

transformable1 :: TransformableTo String
transformable1 = TransformWith show 2.5

transformable2 :: TransformableTo String
transformable2 = TransformWith (uncurry (++)) ("Hello,", " world!")

-- | a. Which type variable is existential inside 'TransformableTo'? What is
-- the only thing we can do to it?

-- | b. Could we write an 'Eq' instance for 'TransformableTo'? What would we be
-- able to check?

instance Eq output => Eq (TransformableTo output) where
  (==) (TransformWith f a) (TransformWith g b) = f a == g b

-- | c. Could we write a 'Functor' instance for 'TransformableTo'? If so, write
-- it. If not, why not?

instance Functor TransformableTo where
  fmap f (TransformWith g a) = TransformWith (f . g) a


{- FOUR -}

-- | Here's another GADT:

data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

-- | a. There's one (maybe two) useful function to write for 'EqPair'; what is
-- it?

equal (EqPair l r) = l == r

notequal (EqPair l r) = l /= r


-- | b. How could we change the type so that @a@ is not existential? (Don't
-- overthink it!)

data EqPair' a where
  EqPair' :: Eq a => a -> a -> EqPair' a


-- | c. If we made the change that was suggested in (b), would we still need a
-- GADT? Or could we now represent our type as an ADT?





{- FIVE -}

-- | Perhaps a slightly less intuitive feature of GADTs is that we can set our
-- type parameters (in this case @a@) to different types depending on the
-- constructor.

data MysteryBox a where
  EmptyBox  ::                                MysteryBox ()
  IntBox    :: Int    -> MysteryBox ()     -> MysteryBox Int
  StringBox :: String -> MysteryBox Int    -> MysteryBox String
  BoolBox   :: Bool   -> MysteryBox String -> MysteryBox Bool

-- | When we pattern-match, the type-checker is clever enough to
-- restrict the branches we have to check to the ones that could produce
-- something of the given type.

getInt :: MysteryBox Int -> Int
getInt (IntBox int _) = int

-- | a. Implement the following function by returning a value directly from a
-- pattern-match:

getInt' :: MysteryBox String -> Int
getInt' (StringBox _ (IntBox int _)) = int

-- | b. Write the following function. Again, don't overthink it!

countLayers :: MysteryBox a -> Int
countLayers box = case box of
  EmptyBox      -> 0
  IntBox    _ _ -> 1
  StringBox _ _ -> 2
  BoolBox   _ _ -> 3

-- | c. Try to implement a function that removes one layer of "Box". For
-- example, this should turn a BoolBox into a StringBox, and so on. What gets
-- in our way? What would its type be?

-- removeLayer box = case box of
-- BoolBox _ b -> b
-- StringBox _ b -> b
-- IntBox _ b -> b
-- mtpybox -> emtpybox



{- SIX -}

-- | We can even use our type parameters to keep track of the types inside an
-- 'HList'!  For example, this heterogeneous list contains no existentials:

data HList a where
  HNil  :: HList ()
  HCons :: head -> HList tail -> HList (head, tail)

exampleHList :: HList (String, (Int, (Bool, ())))
exampleHList = HCons "Tom" (HCons 25 (HCons True HNil))

-- | a. Write a 'head' function for this 'HList' type. This head function
-- should be /safe/: you can use the type signature to tell GHC that you won't
-- need to pattern-match on HNil, and therefore the return type shouldn't be
-- wrapped in a 'Maybe'!

head' :: HList (a, b) -> a
head' (HCons h _) = h

-- | b. Currently, the tuples are nested. Can you pattern-match on something of
-- type @HList (Int, String, Bool, ())@? Which constructor would work?

patternMatchMe :: HList (Int, String, Bool, ()) -> Int
patternMatchMe = undefined

-- | c. Can you write a function that appends one 'HList' to the end of
-- another? What problems do you run into?



{- SEVEN -}

-- | Here are two data types that may help:

data Empty
data Branch left centre right

-- | a. Using these, and the outline for 'HList' above, build a heterogeneous
-- /tree/. None of the variables should be existential.

data HTree a where
  HEmpty :: HTree Empty
  HBranch :: HTree l -> c -> HTree r -> HTree (Branch l c r)

  -- ...

-- | b. Implement a function that deletes the left subtree. The type should be
-- strong enough that GHC will do most of the work for you. Once you have it,
-- try breaking the implementation - does it type-check? If not, why not?

deleft :: HTree (Branch l c r) -> HTree (Branch Empty c r)
deleft (HBranch l c r) = HBranch HEmpty c r


-- | c. Implement 'Eq' for 'HTree's. Note that you might have to write more
-- than one to cover all possible HTrees. You might also need an extension or
-- two, so look out for something... flexible... in the error messages!
-- Recursion is your friend here - you shouldn't need to add a constraint to
-- the GADT!

instance Eq (HTree Empty) where
  (==) _ _ = True

instance (Eq (HTree l), Eq c , Eq (HTree r))
  => Eq (HTree (Branch l c r)) where
  (==) (HBranch l c r ) (HBranch ll cc rr) = l == ll && c == cc && r == rr



{- EIGHT -}

-- | a. Implement the following GADT such that values of this type are lists of
-- values alternating between the two types. For example:
--
-- @
--   f :: AlternatingList Bool Int
--   f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))
-- @

data AlternatingList a b where
  AANil  :: AlternatingList a b
  AACons :: a -> AlternatingList b a -> AlternatingList a b

f :: AlternatingList Bool Int
f = AACons True (AACons 1 (AACons False (AACons 2 AANil)))

g = AACons 1 (AACons False (AACons 1 AANil))
-- | b. Implement the following functions.

getFirsts :: AlternatingList a b -> [a]
getFirsts AANil = []
getFirsts (AACons a rest) = a :  getFirsts skippedRest
  where skippedRest = case rest of
                        AANil -> AANil
                        (AACons _ r) -> r



getSeconds :: AlternatingList a b -> [b]
getSeconds AANil = []
getSeconds (AACons _ rest) = getFirsts rest

-- | c. One more for luck: write this one using the above two functions, and
-- then write it such that it only does a single pass over the list.

foldValues :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues AANil = (mempty, mempty)
foldValues (AACons a rest) = (a <> (fold . getSeconds) rest, (fold . getFirsts) rest)

foldValues' :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues' AANil = (mempty, mempty)
foldValues' (AACons a rest) = let (b , aa) = foldValues rest
                              in (a <> aa, b)




{- NINE -}

-- | Here's the "classic" example of a GADT, in which we build a simple
-- expression language. Note that we use the type parameter to make sure that
-- our expression is well-formed.

data Expr a where
  Equals    :: Expr Int  -> Expr Int            -> Expr Bool
  Add       :: Expr Int  -> Expr Int            -> Expr Int
  If        :: Expr Bool -> Expr a   -> Expr a  -> Expr a
  IntValue  :: Int                              -> Expr Int
  BoolValue :: Bool                             -> Expr Bool

-- | a. Implement the following function and marvel at the typechecker:

eval :: Expr a -> a
eval (Equals x y)          = eval x == eval y
eval (Add    x y)          = eval x + eval y
eval (If bool then' else') = if eval bool
                             then eval then'
                             else eval else'
eval (IntValue x) = x
eval (BoolValue x) = x

-- | b. Here's an "untyped" expression language. Implement a parser from this
-- into our well-typed language. Note that (until we cover higher-rank
-- polymorphism) we have to fix the return type. Why do you think this is?

data DirtyExpr
  = DirtyEquals    DirtyExpr DirtyExpr
  | DirtyAdd       DirtyExpr DirtyExpr
  | DirtyIf        DirtyExpr DirtyExpr DirtyExpr
  | DirtyIntValue  Int
  | DirtyBoolValue Bool

data Typed where
  IntTyped :: Expr Int -> Typed
  BoolTyped :: Expr Bool -> Typed

tidyup :: DirtyExpr -> Maybe Typed
tidyup (DirtyBoolValue b) = Just $ BoolTyped $ BoolValue b
tidyup (DirtyIntValue int) = Just $ IntTyped $ IntValue int
tidyup (DirtyAdd l r) = case (tidyup l, tidyup r) of
  (Just (IntTyped left), Just (IntTyped right)) -> Just $ IntTyped $ Add left right
  _                                               -> Nothing
tidyup (DirtyEquals l r) = case (tidyup l, tidyup r) of
  (Just (IntTyped left), Just (IntTyped right)) -> Just $ BoolTyped $ Equals left right
  _                                               -> Nothing
tidyup (DirtyIf bool then' else') = case (tidyup bool, tidyup then', tidyup else') of
  (Just (BoolTyped bool'), Just (BoolTyped t), Just (BoolTyped e)) -> Just $ BoolTyped $ If bool' t e
  (Just (BoolTyped bool'), Just (IntTyped  t), Just (IntTyped  e)) -> Just $ IntTyped $ If bool' t e
  _                                                                    -> Nothing

parse :: DirtyExpr -> Maybe (Expr Int)
parse exp = case tidyup exp of
  Just (IntTyped smth) -> Just smth
  _                    -> Nothing

-- | c. Can we add functions to our 'Expr' language? If not, why not? What
-- other constructs would we need to add? Could we still avoid 'Maybe' in the
-- 'eval' function?





{- TEN -}

-- | Back in the glory days when I wrote JavaScript, I could make a composition
-- list like @pipe([f, g, h, i, j])@, and it would pass a value from the left
-- side of the list to the right. In Haskell, I can't do that, because the
-- functions all have to have the same type :(

-- | a. Fix that for me - write a list that allows me to hold any functions as
-- long as the input of one lines up with the output of the next.

data TypeAlignedList a b where
  TypeAlignedNil :: TypeAlignedList a a
  TypeAlignedCons :: (a -> b) -> TypeAlignedList b c -> TypeAlignedList a c

a = TypeAlignedCons (const "a") $ TypeAlignedCons read (TypeAlignedCons (+1) TypeAlignedNil)

-- | b. Which types are existential?

-- | c. Write a function to append type-aligned lists. This is almost certainly
-- not as difficult as you'd initially think.

composeTALs :: TypeAlignedList b c -> TypeAlignedList a b -> TypeAlignedList a c
composeTALs TypeAlignedNil b = b
composeTALs a TypeAlignedNil = a
composeTALs xs (TypeAlignedCons g ys)  = TypeAlignedCons g $ composeTALs xs ys

