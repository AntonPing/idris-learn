module SortedList2
import Data.So
import Data.List.Quantifiers
import Control.Relation
import Control.Order

data LessEqual : ty -> (rel : Rel ty) -> Maybe ty -> Type where
    LENothing : LessEqual ty rel Nothing
    LEJust : {rel : Rel ty} -> rel x y ->
        LessEqual x rel (Just y)

data SortedList : (ty : Type) -> (rel : Rel ty) ->  Type
head : SortedList ty rel -> Maybe ty

data SortedList : (ty : Type) -> (rel : Rel ty) ->  Type where
    Nil : SortedList ty rel
    (::) : (x : ty) ->
        (xs : SortedList ty rel) ->
        {auto 0 prf : LessEqual x rel (head xs)} ->
        SortedList ty rel

head [] = Nothing
head (x::xs) = Just x

mutual
    addToList : {rel : Rel ty} -> StronglyConnex ty rel =>
        (x : ty) -> SortedList ty rel -> SortedList ty rel
    addToList x [] = [x]{prf = LENothing}
    addToList x ((y :: ys){prf=prf0}) = 
        case order x y of
            Left prf => (x :: y :: ys) {prf=LEJust prf}
            Right prf => (y :: addToList x ys) {prf = lemma1 y x ys prf prf0}

    lemma1 : {rel : Rel ty} -> StronglyConnex ty rel =>
        (x : ty) -> (y : ty) -> (ys : SortedList ty rel)
        -> (rel x y)
        -> LessEqual x rel (head ys)
        -> LessEqual x rel (head (addToList y ys))
    lemma1 x y [] prf1 prf2 = LEJust prf1
    lemma1 x y (y'::ys') prf1 prf2 with (order {rel} y y') proof odr
        _ | Left _ = LEJust prf1
        _ | Right _ = prf2
    
    -- we don't need lemma2 anymore.
    lemma2 : {rel : Rel ty} -> StronglyConnex ty rel =>
        (x: ty) -> (ys : SortedList {rel} ty)
        -> Either (head (addToList x ys) = (head ys)) (head (addToList x ys) = Just x)
    lemma2 x [] = Right Refl
    lemma2 x (y::_) with (order {rel} x y)
        _ | Left prf = Right Refl
        _ | Right prf = Left Refl