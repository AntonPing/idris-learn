module MetaProg

import Language.Reflection
import Data.Bool.Xor
import Data.Nat

------------------------
--------Home Work-------
------------------------

name : String -> Name
name str = UN $ Basic str

var : String -> TTImp
var str = IVar EmptyFC $ UN $ Basic str

bind : String -> TTImp
bind str = IBindVar EmptyFC str

ap : TTImp -> TTImp -> TTImp
ap l r = IApp EmptyFC l r
infixl 0 `ap`

pi : TTImp -> TTImp -> TTImp
pi l r = IPi EmptyFC MW ExplicitArg Nothing l r
infixl 0 `pi`

foldType : (n : Nat) -> TTImp
foldType 0 = `(Bool)
foldType (S n) = `(Bool) `pi` foldType n

foldLHS : (f : String) -> (n : Nat) -> TTImp
foldLHS f 0 = var f
foldLHS f (S n) = foldLHS f n `ap` bind ("x" ++ show (S n))

foldRHS : (n : Nat) -> (0 _: LTE 1 n) => TTImp
foldRHS 0 = var "???" -- never
foldRHS 1 = var "x1"
foldRHS (S n@(S _)) = `(Data.Bool.Xor.xor) `ap` (var $ "x" ++ show (S n)) `ap` foldRHS n

mkXor : String -> (n : Nat) -> LTE 1 n => Elab ()
mkXor f n =  declare $
    [ IClaim EmptyFC MW Public [] $ MkTy EmptyFC EmptyFC (name f) (foldType n)
    , IDef EmptyFC (name f) [ PatClause EmptyFC (foldLHS f n) (foldRHS n) ]
    ]

%language ElabReflection

failing "Can't find an implementation for LTE 1 0"
    %runElab mkXor "xor0" 0

%runElab mkXor "xor1" 1
%runElab mkXor "xor2" 2
%runElab mkXor "xor3" 3
%runElab mkXor "xor4" 4
%runElab mkXor "xor5" 5

test1 : MetaProg.xor3 True False False = True
test1 = Refl

test2 : MetaProg.xor3 True True False = False
test2 = Refl

test3 : MetaProg.xor3 True True True = True
test3 = Refl

test4 : MetaProg.xor4 True True True True = False
test4 = Refl

test5 : MetaProg.xor5 True True True True False = False
test5 = Refl