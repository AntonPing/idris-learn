module SortedList2
import Data.So
import Data.List.Quantifiers
import Control.Relation
import Control.Order

mutual
    data SortedList : {rel : Rel ty} -> (ty : Type) -> Type where
        Nil : SortedList ty
        (::) : -- {rel : Rel ty} -> 
            (x : ty) -> (xs : SortedList {rel} ty)
            -> {auto prf : LessEqual {rel} x (head xs)}
            -> SortedList {rel} ty
    
    data LessEqual : {rel : Rel ty} -> ty -> Maybe ty -> Type where
        LENothing : LessEqual ty Nothing
        LEJust : {rel : Rel ty} -> 
            rel x y -> LessEqual x {rel} (Just y)
    
    head : SortedList {rel} ty -> Maybe ty
    head [] = Nothing
    head (x::xs) = Just x

mutual
    addToList : {rel : Rel ty} -> StronglyConnex ty rel =>
        (x : ty) -> SortedList {rel} ty -> SortedList {rel} ty
    addToList x [] = [x]{prf = LENothing}
    addToList x ((y :: ys){prf=prf0}) = 
        case order x y of
            Left prf => (x :: y :: ys) {prf=LEJust prf}
            Right prf => (y :: addToList x ys) {prf = lemma1 prf prf0}

    lemma1 : {rel : Rel ty} -> StronglyConnex ty rel =>
        {x : ty} -> {y : ty} -> {ys : SortedList {rel} ty}
        -> (rel x y)
        -> LessEqual {rel} x (head ys)
        -> LessEqual {rel} x (head (addToList y ys))
    lemma1 @{sc} prf1 prf2 with (ys)
        _ | [] = LEJust prf1
        _ | (y'::ys') with (order @{sc} y y') proof odr -- why can't just (order y y')?
            _ | Left prf3 = LEJust prf1
            _ | Right prf4 = prf2
    
    -- we don't need lemma2 anymore.
    lemma2 : {rel : Rel ty} -> StronglyConnex ty rel =>
        {x: ty} -> {ys : SortedList {rel} ty}
        -> Either (head (addToList x ys) = (head ys)) (head (addToList x ys) = Just x)
    lemma2 @{sc} {x} with (ys)
        _ | [] = Right Refl
        _ | (y::_) with (order @{sc} x y) -- why can't just (order x y)?
            _ | Left prf = Right Refl
            _ | Right prf = Left Refl