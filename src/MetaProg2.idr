module MetaProg2

import Debug.Trace
import Data.Bool.Xor
import Language.Reflection

%default total
%language ElabReflection

{-
interface X x where
  mkXor : x
  xor' : Bool -> x -> x

X Bool where
  mkXor = False
  xor' = xor

X a => X (Bool -> a) where
   mkXor = \b => xor' b mkXor
   xor' b f b' = f (b `xor` b')
-}

{-
foldType : (n : Nat) -> Type
foldType 0 = Bool
foldType (S n) = Bool -> foldType n

mkXor' : {auto n : Nat} -> foldType n
mkXor' {n=0} = False
mkXor' {n=1} = id
mkXor' {n=S(S(n'))} = \a => mkXor' {n=S(n')} . (`xor` a)

xor1 : Bool -> Bool
xor1 = mkXor' {n=1}

xor2 : Bool -> Bool -> Bool
xor2 = mkXor' {n=2}

xor3 : Bool -> Bool -> Bool -> Bool
xor3 = mkXor' {n=3}
-}

var : String -> TTImp
var str = IVar EmptyFC $ UN $ Basic str

bind : String -> TTImp
bind str = IBindVar EmptyFC str

lam : String -> TTImp -> TTImp
lam str rhs = ILam EmptyFC MW ExplicitArg (Just $ UN $ Basic str) (var "Bool") rhs

ap : TTImp -> TTImp -> TTImp
ap lhs rhs = IApp EmptyFC lhs rhs
infixl 0 `ap`

pi : TTImp -> TTImp -> TTImp
pi lhs rhs = IPi EmptyFC MW ExplicitArg Nothing lhs rhs
infixl 0 `pi`

foldBody : (n : Nat) -> TTImp
foldBody 0 = var "False"
foldBody 1 = var "x1"
foldBody (S n@(S _)) = `(Data.Bool.Xor.xor) `ap` (var $ "x" ++ show (S n)) `ap` foldBody n

foldArgs : (n : Nat) -> TTImp -> TTImp
foldArgs 0 body = body
foldArgs (S n) body = lam ("x" ++ show (S n)) (foldArgs n body)

foldXor : (n : Nat) -> TTImp
foldXor n = foldArgs n (foldBody n)

checkAllBool : TTImp -> Elab Nat
checkAllBool $ IPi fc cnt exp mn lhs rhs = do
  lhsTy <- check {expected=Type} lhs
  case lhsTy of
    Bool => pure ()
    _ => failAt (getFC lhs) "Expected Bool"
  (+ 1) <$> checkAllBool rhs
checkAllBool xs = do
  ty <- check {expected = Type} xs
  case ty of
    Bool => pure 0
    _ => failAt (getFC xs) "Expected Bool"

mkXor : Elab a
mkXor = do
  ttimp <- goal
  ttimp <- case ttimp of
    Just x => pure x
    Nothing => fail "Failed"
  k <- checkAllBool ttimp
  check {expected=a} (foldXor k)

xor1 : (a : Bool) -> Bool
xor1 = %runElab mkXor

xor2 : (a, b : Bool) -> Bool
xor2 = %runElab mkXor

xor3 : (a, b, c : Bool) -> Bool
xor3 = %runElab mkXor

xor4 : (a, b, c, d : Bool) -> Bool
xor4 = %runElab mkXor

xor5 : (a, b, c, d, e : Bool) -> Bool
xor5 = %runElab mkXor

test1 : MetaProg2.xor3 True False False = True
test1 = Refl

test2 : MetaProg2.xor3 True True False = False
test2 = Refl

test3 : MetaProg2.xor3 True True True = True
test3 = Refl

test4 : MetaProg2.xor4 True True True True = False
test4 = Refl

test5 : MetaProg2.xor5 True True True True False = False
test5 = Refl

main : IO ()
main = do
  putStrLn $ show $ foldXor 3
