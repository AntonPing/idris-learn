module SortedList
import Data.So
import Data.List.Quantifiers

lessEqual : Ord ty => ty -> Maybe ty -> Bool
lessEqual x (Nothing) = True
lessEqual x (Just y) = (x <= y)

namespace A
    mutual
        data SortedList : (ty : Type) -> Ord ty => Type where
            Nil : Ord ty => SortedList ty
            (::) : Ord ty => (x : ty) -> (xs : SortedList ty)
                -> {auto prf : So (lessEqual x (head xs))} -> SortedList ty
        
        head : Ord ty => SortedList ty -> Maybe ty
        head [] = Nothing
        head (x::xs) = Just x

namespace B
    data SortedList : (ty : Type) -> Ord ty => (hd : Maybe ty) -> Type where
        Nil : Ord ty => SortedList ty Nothing
        (::) : Ord ty => {hd : Maybe ty} -> (x : ty) -> (xs : SortedList ty hd)
            -> {auto prf : So (lessEqual x hd)} -> SortedList ty (Just x)

mutual
    data SortedList : (ty : Type) -> Ord ty => Type where
        Nil : Ord ty => SortedList ty
        (::) : Ord ty => (x : ty) -> (xs : SortedList ty)
            -> {auto prf : So (lessEqual x (head xs))} -> SortedList ty
    
    head : Ord ty => SortedList ty -> Maybe ty
    head [] = Nothing
    head (x::xs) = Just x

mutual
    addToList : Ord ty => (x : ty) -> SortedList ty -> SortedList ty
    addToList x [] = [x]
    addToList x ((::) y ys {prf}) with (x <= y) proof lte
        _ | True =
            (::) x {prf = rewrite lte in Oh} $ (y::ys)
        _ | False = 
            (::) y {prf = lemma1 lte prf} $ addToList x ys

    lemma1 : Ord ty => {x: ty} -> {y: ty} -> {ys : SortedList ty}
        -> (x <= y = False)
        -> So (lessEqual y (head ys))
        -> So (lessEqual y (head (addToList x ys)))
    lemma1 lte prf with (lessEqual y (head ys)) proof prf2
        _ | True with (head (addToList x ys)) proof prf3
            _ | hd = case lemma2 {ys} of {- why can't just lemma2? -}
                Left prf4 => do
                    rewrite trans (sym prf3) prf4
                    rewrite prf2
                    Oh
                Right prf4 => do
                    rewrite trans (sym prf3) prf4
                    ?TRIVIAL {- how to proof this? -}

    lemma2 : Ord ty => {x: ty} -> {ys : SortedList ty}
        -> Either (head (addToList x ys) = (head ys)) (head (addToList x ys) = Just x)
    lemma2 with (ys) proof prf
        _ | [] = Right Refl
        _ | (y::_) with (x <= y)
            _ | True = Right Refl
            _ | False = Left Refl

{-
addToList x (y1 :: y2 :: ys) with (x <= y1) proof prf
    _ | True = 
        (::) x {prf = rewrite prf in Oh} (y1 :: y2 :: ys)
    _ | False =
        (::) y1 {prf = ?H2} (addToList x (y2 :: ys))
-}
{-
data SortedList : (ty : Type) -> (ord : Ord ty) => (hd : Maybe ty) -> Type where
    Nil : (ord : Ord ty) => SortedList ty Nothing
    (::) : (ord : Ord ty) => {hd : Maybe ty} -> (x : ty) -> (xs : SortedList ty hd)
        -> {auto prf : So (lessEqual x hd)} -> SortedList ty (Just x)

addToList : (ord : Ord ty) => {hd : Maybe ty} -> (a : ty) -> SortedList ty hd
    -> SortedList ty (if lessEqual a hd then Just a else hd)
addToList a [] = [a]
addToList a ((::) x xs {prf}) with (a <= x) proof lte
    _ | False = (::) x (addToList a xs) {prf = ?pp}
        {-
            with (lessEqual a hd) proof lhd
            _ | False = do
                -- rewrite lhd
                ?KK
            _ | True = do
                let ys = addToList a xs
                -- (::) x ys {prf = ?pp}
                ?KK2
        -}
    _ | True = (::) a (x::xs) {prf = rewrite lte in Oh}
-}


{-
data SortedList : {ord : Ord ty} -> (ty : Type) -> Type where
    Nil : SortedList ty
    (::) : (x : ty) -> (xs : SortedList {ord} ty)
        -> {auto prf : So (lessEqual @{ord} x xs)} -> SortedList {ord} ty

SortedList : (ty : Type) -> Ord ty => Type
SortedList ty = (xs : List ty ** All (\x => So $ hd <= x) xs) 

SortedNil : Ord ty => SortedList ty
SortedNil = ([] ** )
-}