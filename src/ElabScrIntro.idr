module ElabScrIntro

import Control.Function.FunExt
import Data.Maybe
import Language.Reflection

x : Name
x = `{anyName}

y : Name
y = `{Prelude.Types.Nat}

expr1 : TTImp
expr1 = `( function arg1 arg2 )

expr1' : TTImp
expr1' = IApp EmptyFC (IApp EmptyFC (IVar EmptyFC $ UN $ Basic "function") (IVar EmptyFC $ UN $ Basic "arg1")) (IVar EmptyFC $ UN $ Basic "arg2")

decls : List Decl
decls = `[  f : Nat -> Nat
            g x d = f 5 + 34
            f 0 z = 234
            g 0 z with (sdf)
              g 0 z | xx = 234
            data X : Type
            data X : Type where
              MkX : Nat -> X
            parameters {x : Nat}
              f : Nat -> Nat
              f y = x + y + 34
            %transform "sdf" asfd = d
            %logging "sdf" 3

         ]

------------

data OurGoodType = MkO Nat

isSemigroup : Type -> Elab Bool
isSemigroup a = do
  q <- quote a
  t <- check `(Semigroup ~q)
  isJust <$> search t

%language ElabReflection

before : Bool
before = %runElab isSemigroup OurGoodType

Semigroup OurGoodType where
  MkO l <+> MkO r = MkO $ l + r

after : Bool
after = %runElab isSemigroup OurGoodType

-- why this version doen't work?
-- b_corr : before = False
-- b_corr = Refl

b_corr : ElabScrIntro.before = False
b_corr = Refl

a_corr : ElabScrIntro.after = True
a_corr = Refl

---------
declareF : Elab ()
declareF =
  declare `[ f : Nat -> Nat -> Nat
             f x Z = x + 2
             f x y = x + y
           ]

failing "Undefined name f"
  ff : Nat
  ff = f 4 5

%runElab declareF

ff : Nat
ff = f 4 5

ff_corr : ElabScrIntro.ff = 9
ff_corr = Refl

ap : TTImp -> TTImp -> TTImp
ap l r = IApp EmptyFC l r

infixl 0 `ap`

declareX : Name -> Elab ()
declareX nm =
  declare
    [ IClaim EmptyFC MW Public [] $ MkTy EmptyFC EmptyFC nm `(Nat -> Nat -> Nat)
    , IDef EmptyFC nm
      [ PatClause EmptyFC (IVar EmptyFC nm `ap` IBindVar EmptyFC "x" `ap` IVar EmptyFC `{Z}) `(x + 2)
      , PatClause EmptyFC (IVar EmptyFC nm `ap` IBindVar EmptyFC "x" `ap` IBindVar EmptyFC "y") `(x + y)
      ]
    ]

%runElab declareX `{f2}

declareX_corr : FunExt => ElabScrIntro.f = ElabScrIntro.f2
declareX_corr = funExt $ \case
  Z => funExt $ \case
    0   => Refl
    S k => Refl
  S k => funExt $ \case
    0   => Refl
    S j => Refl
