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

correspond1 : Eq a =>
    (xs : List a) ->
    (x : a) ->
    case find xs x of
        Nothing  => Unit
        Just idx => So $ indF xs idx == x

correspond2 : Eq a =>
    (xs : List a) ->
    (x : a) ->
    (idx : Fin $ length xs) ->
    find xs x = Just idx ->
    So $ indF xs idx == x

correspond3 : Eq a =>
    (xs : List a) ->
    (x : a) ->
    Either (find xs x = Nothing) (So $ (indF xs <$> (find xs x)) == Just x)

justInject : Just a = Just b -> a = b
justInject Refl = Refl

corr1ToCorr2 : Eq a =>
    (indF : (xs : List a) -> Fin (length xs) -> a) ->
    (find : (zs : List a) -> a -> Maybe $ Fin $ length zs) ->
    (
        (xs : List a) -> (x : a) ->
        case find xs x of
            Nothing  => Unit
            Just idx => So $ indF xs idx == x
    ) ->
    (
        (xs : List a) -> (x : a) -> 
        (idx : Fin $ length xs) ->
        find xs x = Just idx ->
        So $ indF xs idx == x
    )

{-
corr1ToCorr2 indF find lem xs x idx fltr = do
    let prf = lem xs x
    -- my first try, can't rewrite context
    -- rewrite fltr
    ?HOLE
--}

corr1ToCorr2 indF find thrm xs x idx fltr with (thrm xs x) | (find xs x)
    _ | _ | Nothing impossible
    _ | thrm' | Just k = rewrite sym $ justInject fltr in thrm'
    
corr2ToCorr1 : Eq a =>
    (indF : (xs : List a) -> Fin (length xs) -> a) ->
    (find : (zs : List a) -> a -> Maybe $ Fin $ length zs) ->
    (
        (xs : List a) -> (x : a) -> 
        (idx : Fin $ length xs) ->
        find xs x = Just idx ->
        So $ indF xs idx == x
    ) ->
    (
        (xs : List a) -> (x : a) ->
        case find xs x of
            Nothing  => Unit
            Just idx => So $ indF xs idx == x
    ) 
corr2ToCorr1 indF find thrm xs x with (find xs x) proof prf1
    _ | Nothing = ()
    _ | Just k = thrm xs x k prf1

corr1ToCorr3 : Eq a =>
    (indF : (xs : List a) -> Fin (length xs) -> a) ->
    (find : (zs : List a) -> a -> Maybe $ Fin $ length zs) ->
    (
        (xs : List a) -> (x : a) ->
        case find xs x of
            Nothing  => Unit
            Just idx => So $ indF xs idx == x
    ) ->
    (
        (xs : List a) -> (x : a) ->
        Either (find xs x = Nothing) (So $ (indF xs <$> (find xs x)) == Just x)
    )
corr1ToCorr3 indF find thrm xs x with (thrm xs x) | (find xs x)
    _ | _ | Nothing = Left Refl
    _ | thrm' | Just k = Right thrm'

corr3ToCorr1 : Eq a =>
    (indF : (xs : List a) -> Fin (length xs) -> a) ->
    (find : (zs : List a) -> a -> Maybe $ Fin $ length zs) ->
    (
        (xs : List a) -> (x : a) ->
        Either (find xs x = Nothing) (So $ (indF xs <$> (find xs x)) == Just x)
    ) ->
    (
        (xs : List a) -> (x : a) ->
        case find xs x of
            Nothing  => Unit
            Just idx => So $ indF xs idx == x
    )
corr3ToCorr1 indF find thrm xs x with (thrm xs x) | (find xs x)
    _ | _ | Nothing = ()
    _ | Left prf | Just k = absurd $ prf
    _ | Right prf | Just k = prf