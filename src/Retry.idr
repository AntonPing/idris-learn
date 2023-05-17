module Retry

import Language.Reflection

%default total

%language ElabReflection

summonNat : Name -> Elab Nat
summonNat nm = do
    let inter : TTImp := IVar EmptyFC nm
    check inter

namespace X

    N1 : Nat
    N1 = 5

    XX : Nat
    XX = %runElab summonNat `{N1}

    X_XX_corr : XX = 5
    X_XX_corr = Refl

namespace Y

    N1 : Nat
    N1 = 7

    export
    XX : Nat
    XX = %runElab summonNat `{N1}

    Y_XX_corr : XX = 7
    Y_XX_corr = Refl

--Y_XX_corr : XX = 7
--Y_XX_corr = Refl

---

summonNat' : Name -> Elab Nat
summonNat' nm = do
    let inter : TTImp := IVar EmptyFC nm
    check inter <|> fail "Name `\{show nm}` is not a proper Nat"

N3 : String
N3 = "2"

failing "not a proper Nat"

    XX : Nat
    XX = %runElab summonNat' `{N3}

---

checkAllBool : TTImp -> Elab Type
checkAllBool $ IPi fc cnt exp mn lhs rhs = do
    lhsTy <- check {expected=Type} lhs
    case lhsTy of
        Bool => pure ()
        _ => failAt (getFC lhs) "Expected Bool"
    checkAllBool rhs
checkAllBool xs = check xs

checkAllBool' : TTImp -> Elab Type
checkAllBool' $ IPi fc cnt exp mn lhs rhs = do
    case lhs of
        IVar fc n => when (not $ n == `{Bool} || n == `{Prelude.Bool} || n == `{Prelude.Types.Bool}) $ failAt fc "Expected Bool"
        _ => failAt (getFC lhs) "Expected Bool"
    checkAllBool rhs
checkAllBool' xs = check xs

x : Type
x = %runElab checkAllBool `(Nat)

y : Type
y = %runElab checkAllBool `(Bool -> Nat)

B : Type
B = Bool

y' : Type
y' = %runElab checkAllBool `(B -> Nat)

y'' : Type
y'' = %runElab checkAllBool `((0 _ : B) -> Nat)

failing "Expected Bool"

    z : Type
    z = %runElab checkAllBool `(Char -> Nat)

failing "Expected Bool"

    z' : Type
    z' = %runElab checkAllBool `(Bool -> Char -> Nat)

---

interface IX x where
    ix : x -> Nat

interface IY y where
    iy : String -> y -> Nat

interface DefaultString where
    defaultString : String



magicF : (x : a) -> (defaultDefault : String) -> Elab Nat
magicF x defaultDefault =
    (check {expected=IX a} `(%search) >>= \_ =>
        pure $ ix x
    ) <|> (
        (check {expected=IY a} `(%search) >>= \_ =>
            (check {expected = DefaultString} `(%search) >>= \_ =>
                pure $ iy defaultString x
            ) <|> (
                pure $ iy defaultDefault x
            )
        ) <|> (do
            q <- quote x
            aExpr <- quote a
            failAt (getFC q) "No IX or IY found for \{show aExpr}"
        )
    )

magicF' : (x : a) -> (defaultDefault : String) -> Elab Nat
magicF' x defaultDefault = do
            (\_ => ix x) <$> check {expected=IX a} `(%search)
    <|> (check {expected=IY a} `(%search) >>= \_ => do
--        str <- check `(defaultString) <|> pure defaultDefault
                str <- (check {expected=DefaultString} `(%search) <&> \_ => defaultString) <|> pure defaultDefault
                pure $ iy str x
            )
    <|> do
        q <- quote x
        aExpr <- quote a
        failAt (getFC q) "No IX or IY found for \{show aExpr}"
