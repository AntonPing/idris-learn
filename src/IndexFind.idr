module IndexFind
import Data.Fin
import Data.List.Quantifiers

%default total

indF : (xs : List a) -> Fin (length xs) -> a
indF (x::xs) FZ     = x
indF (x::xs) (FS y) = indF xs y

find : Eq a => (xs : List a) -> (x : a) -> Maybe $ Fin $ length xs
find []      y = Nothing
find (x::xs) y = if x == y then Just 0 else FS <$> find xs y

-- if_no_then_nothing' : Eq a => (xs : List a) -> (y : a) -> All (\x => Not $ So $ x == y) xs -> find xs y = Nothing

if_no_then_nothing  : Eq a => (xs : List a) -> (y : a) -> All (\x => So $ not $ x == y) xs -> find xs y = Nothing
if_no_then_nothing [] _ _ = Refl
if_no_then_nothing (x::xs) y (p::ps) with (x == y)
    _ | False with (find xs y) proof prf1 | (if_no_then_nothing xs y ps)
        _ | (Just b) | prf2 = absurd $ trans (sym prf1) prf2
        _ | Nothing | _ = Refl
    _ | True impossible

{-
if_no_then_nothing' : Eq a => (xs : List a) -> (y : a) -> All (\x => Not $ So $ x == y) xs -> find xs y = Nothing

if_no_then_nothing  : Eq a => (xs : List a) -> (y : a) -> All (\x => So $ not $ x == y) xs -> find xs y = Nothing
if_no_then_nothing []      _ _       = Refl
if_no_then_nothing (x::xs) y (p::ps) with (x == y)
  _ | False with (if_no_then_nothing xs y ps) | (find xs y)
    _ | prf | Nothing = Refl
-}



