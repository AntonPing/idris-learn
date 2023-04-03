module TypedForth
import Data.Vect
import Data.Fin

data HVect : Vect n Type -> Type where
    Nil  : HVect []
    (::) : (x : ty) -> HVect tys -> HVect (ty :: tys)

index : (k : Fin n) -> HVect tys -> index k tys
index _ [] impossible
index FZ (x::xs) = x
index (FS k') (x::xs) = index k' xs

dropVect : Fin (S n) -> Vect (S n) a -> Vect n a
dropVect FZ (x :: xs) = xs
dropVect (FS FZ) (x :: y :: xs) = x :: xs
dropVect (FS (FS n')) (x :: y :: xs) = x :: dropVect (FS n') (y::xs)

dropHVect : {0 tys: Vect (S n) Type} ->
    (k : Fin (S n)) -> HVect tys -> HVect (dropVect k tys)
dropHVect FZ (x :: xs) = xs
dropHVect (FS FZ) (x :: y :: xs) = x :: xs
dropHVect (FS (FS n')) (x :: y :: xs) = x :: dropHVect (FS n') (y::xs)

data ForthExpr : (stk : Vect n Type) -> Type where
    Start : ForthExpr []
    Lit : (x : ty) ->
        ForthExpr stk -> ForthExpr (ty :: stk)
    UnOp : (f : ty1 -> ty2) ->
        ForthExpr (ty1 :: stk) ->  ForthExpr (ty2 :: stk)
    BinOp : (f : ty1 -> ty2 -> ty3) ->
        ForthExpr (ty1 :: ty2 :: stk) -> ForthExpr (ty3 :: stk)
    Over : (k : Fin n) ->
        ForthExpr stk -> ForthExpr (index k stk :: stk)
    Drop : (k : Fin (S n)) ->
        ForthExpr stk -> ForthExpr (dropVect k stk)

runForth : {0 stk: Vect n Type} -> ForthExpr stk -> HVect stk
runForth Start = []
runForth (Lit lit next) =
    (lit :: runForth next)
runForth (UnOp f next) =
    let (x::xs) = runForth next in f x :: xs
runForth (BinOp f next) =
    let (x::y::xs) = runForth next in f x y :: xs
runForth (Over k next) = 
    let stk = runForth next in (index k stk :: stk)
runForth (Drop k next) =
    let stk = runForth next in dropHVect k stk

infixr 10 :-
(:-) : (a -> b) -> (b -> c) -> (a -> c)
(:-) = flip (.)

dup : ForthExpr (ty :: stk) -> ForthExpr (ty :: ty :: stk)
dup = Over 0

drop : ForthExpr (ty1 :: stk) -> ForthExpr stk
drop = Drop 0

swap : ForthExpr (ty1 :: ty2 :: stk) -> ForthExpr (ty2 :: ty1 :: stk)
swap =  (Over 1 :- Drop 2)

muladd : ForthExpr (Integer :: Integer :: Integer :: stk) -> ForthExpr (Integer :: stk)
muladd = BinOp (+) :- BinOp (*)

test : ForthExpr stk -> ForthExpr (Integer :: Integer :: stk)
test = Lit 1 :- Lit 2 :- Lit 3 :- dup :- swap :- muladd

data Wrapper : Type -> Type where
    Wrap : (x : ty) -> Wrapper ty

Show ty => Show (Wrapper (HVect [ty])) where
    show (Wrap [x]) = show x

(Show ty, Show (Wrapper (HVect tys))) => Show (Wrapper (HVect (ty::tys))) where
    show (Wrap (x::xs)) = show x ++ "," ++ show (Wrap xs)

Show (HVect []) where
    show [] = "[]"

Show (Wrapper (HVect tys)) => Show (HVect tys) where
    show vec = "[" ++ (show $ Wrap vec) ++ "]"

export
runTest : IO ()
runTest = printLn $ runForth $ test Start
