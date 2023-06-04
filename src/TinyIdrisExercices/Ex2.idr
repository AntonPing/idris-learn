import Data.Nat

data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

-- In the term representation, we represent local variables as an index into
-- a list of bound names:
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

-- And, sometimes, it's convenient to manipulate variables separately.
-- Note the erasure properties of the following definition (it is just a Nat
-- at run time)
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

-- 1. Remove all references to the most recently bound variable
tryDrop : Var (v :: vs) -> Maybe (Var vs)
tryDrop (MkVar {i = 0} prf) = Nothing
tryDrop (MkVar {i = S i'} (Later prf)) = Just $ MkVar {i = i'} prf

dropFirst : List (Var (v :: vs)) -> List (Var vs)
dropFirst xs = mapMaybe tryDrop xs


-- 2. Add a reference to a variable in the middle of a scope - we'll need 
-- something like this later.
-- Note: The type here isn't quite right, you'll need to modify it slightly.
weakenN : {outer : _} -> IsVar n i vars -> IsVar n (length outer + i) (outer ++ vars)
weakenN {outer} var with (outer) proof prf
    _ | [] = var
    _ | x :: xs = Later $ weakenN var

-- try comment {outer} or {i} in the lhs of pattern match, they behave differently
weakenNVar : {outer : _} -> Var vs -> Var (outer ++ vs)
weakenNVar {outer} (MkVar {i} var) = (MkVar {i = length outer + i} (weakenN var))

embedN : IsVar n i vars -> IsVar n i (vars ++ inner)
embedN First = First
embedN (Later prf) = Later (embedN prf)

embedNVar : Var vs -> Var (vs ++ inner)
embedNVar (MkVar var) = (MkVar (embedN var))

{-
getIsVarI : IsVar n i ns -> (i' : Nat ** i = i') 
getIsVarI First = (0 ** Refl)
getIsVarI (Later var) = do
    let (i' ** prf) = getIsVarI var
    (S i' ** cong S prf)
-}

insertN : {outer, ns, i1 : _} ->
    IsVar n i1 (outer ++ inner) -> (i2 ** IsVar n i2 (outer ++ (ns ++ inner)))
insertN {outer = []} {i1} var = (length ns + i1 ** weakenN var)
insertN {outer = x :: xs} First = (0 ** First)
insertN {outer = x :: xs} (Later prf) = do
    let (i' ** prf') = insertN {outer = xs} prf
    (S i' ** Later prf')

insertVar : {ns : List Name} -> {outer : _} ->
    Var (outer ++ inner) -> Var (outer ++ (ns ++ inner))
insertVar (MkVar var) = do
    -- let (i' ** prf) = insertN var
    -- MkVar {i=i'} prf
    ?HOLE
    
{-
data QuantTest : Nat -> Type where
    PlaceHolder : (0 n : Nat) -> QuantTest n

-- this is okey!
quantityTest1 : QuantTest n -> QuantTest (S n)
quantityTest1 (PlaceHolder arg) = PlaceHolder (S arg)

-- but this is not okey??
quantityTest2 : QuantTest n -> QuantTest (S n)
quantityTest2 (PlaceHolder arg) = do
    let 0 arg' : Nat
        arg' = S arg
    PlaceHolder (arg')
-}