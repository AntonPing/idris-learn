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

indf_after_find :  Eq a =>
    (xs : List a) -> (y : a) ->
    Either (find xs y = Nothing) (So $ (indF xs <$> (find xs y)) == Just y)
indf_after_find [] y = Left Refl
indf_after_find (x::xs') y with (x == y) proof prf
    _ | True = Right $ rewrite prf in Oh
    _ | False with (indf_after_find xs' y)
        _ | Left prf1  = Left $ rewrite prf1 in Refl
        _ | Right prf2 with (find xs' y)
            _ | Just k = Right prf2
-- change 'k' to 'a', something wired happens
--          _ | Just a = ?HOLE
            _ | Nothing = Left Refl

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



