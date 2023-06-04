import Decidable.Equality
import Control.Function

-- This is the (simplified) definition of names in Core.TT
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

-- 1. Write an Eq instance for Name
-- (sorry, it's not derivable yet!)
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x i) (MN y j) = x == y && i == j
  (==) _ _ = False

-- 2. Sometimes, we need to compare names for equality and use a proof that
-- they're equal. So, implement the following 
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN x) (UN x) | (Yes Refl) = Just Refl
  _ | _ = Nothing
nameEq (MN x i) (MN y j) with (decEq x y) | (decEq i j)
  nameEq (MN x i) (MN x i) | (Yes Refl) | (Yes Refl) = Just Refl
  _ | _ | _ = Nothing
nameEq _ _ = Nothing

{-
nameEq' : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq' (UN x) (UN x) = ?HOLE
-}

Injective UN where
  injective prf with (prf)
    injective prf | Refl = Refl

Biinjective MN where
  biinjective prf with (prf)
    biinjective prf | Refl = (Refl, Refl)

Uninhabited (UN x = MN y j) where
  uninhabited prf impossible

Uninhabited (MN x i = UN y) where
  uninhabited prf impossible

-- 3. (Optional, since we don't need this in Idris 2, but it's a good
-- exercise to see if you can do it!) Implement decidable equality, so you
-- also have a proof if names are *not* equal.
DecEq Name where
  -- decEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)
  decEq (UN x) (UN y) with (decEq x y)
    decEq (UN x) (UN x) | (Yes Refl) = Yes Refl
    decEq (UN x) (UN y) | (No ctr1) = No $ \ctr2 => ctr1 $ injective ctr2
  decEq (MN x i) (MN y j) with (decEq x y) | (decEq i j)
    decEq (MN x i) (MN x i) | (Yes Refl) | (Yes Refl) = Yes Refl
    decEq (MN x i) (MN y j) | _ | (No ctr1) = No $ \ctr2 => ctr1 $ (snd . biinjective) ctr2
    decEq (MN x i) (MN y j) | (No ctr1) | _ = No $ \ctr2 => ctr1 $ (fst . biinjective) ctr2
  decEq (UN x) (MN y j) = No $ \ctr => absurd ctr
  decEq (MN x j) (UN y) = No $ \ctr => absurd ctr
