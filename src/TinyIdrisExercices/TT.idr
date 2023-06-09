module TinyIdrisExercices.TT

import Data.List
import Data.DPair
import Data.Maybe
import Decidable.Equality

-- In Idris2, this is defined in Core.Name
public export
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

export
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN y) (UN y) | (Yes Refl) = Just Refl
  nameEq (UN x) (UN y) | (No contra) = Nothing
nameEq (MN x t) (MN x' t') with (decEq x x')
  nameEq (MN x t) (MN x t') | (Yes Refl) with (decEq t t')
    nameEq (MN x t) (MN x t) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN x t) (MN x t') | (Yes Refl) | (No contra) = Nothing
  nameEq (MN x t) (MN x' t') | (No contra) = Nothing
nameEq _ _ = Nothing

export
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x i) (MN y j) = i == j && x == y
  (==) _ _ = False

nameTag : Name -> Int
nameTag (UN _) = 0
nameTag (MN _ _) = 1

export
Ord Name where
  compare (UN x) (UN y) = compare x y
  compare (MN x i) (MN y j) =
    case compare x y of
      EQ => compare i j
      t => t
  compare x y = compare (nameTag x) (nameTag y)

public export
data NameType : Type where
     Func : NameType
     Bound : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon : (tag : Int) -> (arity : Nat) -> NameType

export
Show NameType where
  show Func = "Func"
  show (DataCon t a) = "DataCon " ++ show (t, a)
  show (TyCon t a) = "TyCon " ++ show (t, a)
  show Bound = "Bound"

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
dropVar : (ns : List Name) -> {idx : Nat} ->
          (0 p : IsVar name idx ns) -> List Name

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

public export
data PiInfo : Type where
     Implicit : PiInfo
     Explicit : PiInfo

public export
data Binder : Type -> Type where
     Lam : PiInfo -> ty -> Binder ty
     Pi : PiInfo -> ty -> Binder ty

     PVar : ty -> Binder ty -- pattern bound variables ...
     PVTy : ty -> Binder ty -- ... and their type

export
Functor Binder where
  map func (Lam x ty) = Lam x (func ty)
  map func (Pi x ty) = Pi x (func ty)
  map func (PVar ty) = PVar (func ty)
  map func (PVTy ty) = PVTy (func ty)

public export
data Term : List Name -> Type where
     Local : (idx : Nat) -> -- de Bruijn index
             (0 p : IsVar name idx vars) -> -- proof that index is valid
             Term vars
     Ref : NameType -> Name -> Term vars -- a reference to a global name
     Meta : Name -> List (Term vars) -> Term vars
     Bind : (nm : Name) -> -- any binder, e.g. lambda or pi
            Binder (Term vars) ->
            (scope : Term (nm :: vars)) -> -- one more name in scope
            Term vars
     App : Term vars -> Term vars -> Term vars -- function application
     TType : Term vars
     Erased : Term vars

-- try to remove a name in vars

removeVar : {inner, x, outer : _} ->
  Var (inner ++ [x] ++ outer) -> Maybe (Var (inner ++ outer))
removeVar {inner = []} (MkVar First) = Nothing
removeVar {inner = []} (MkVar (Later p)) = Just $ MkVar p
removeVar {inner = a::as} (MkVar First) = Just $ MkVar First
removeVar {inner = a::as} (MkVar (Later p)) = do
  MkVar p' <- removeVar {inner = as} (MkVar p)
  pure $ MkVar (Later p')

removeBinder : {inner, x, outer : _} ->
  Binder (Term (inner ++ [x] ++ outer)) -> Maybe (Binder (Term (inner ++ outer)))
  
removeTerm : {inner, x, outer : _} ->
  Term (inner ++ [x] ++ outer) -> Maybe (Term (inner ++ outer))

removeBinder (Lam info ty) = Lam info <$> removeTerm ty
removeBinder (Pi info ty) = Pi info <$> removeTerm ty
removeBinder (PVar ty) = PVar <$> removeTerm ty
removeBinder (PVTy ty) = PVTy <$> removeTerm ty

removeTerm (Local idx p) = do
  MkVar {i=i'} p' <- removeVar (MkVar p)
  pure $ Local i' p'
removeTerm (Ref ty n) = Just $ Ref ty n
removeTerm (Meta n xs) = do
  xs' <- traverse removeTerm xs
  Just $ Meta n xs'
removeTerm (Bind nm bd scope) = do
  bd' <- removeBinder bd
  scope' <- removeTerm {inner = nm::inner} scope
  pure $ Bind nm bd' scope'
removeTerm (App lhs rhs) = do
  lhs' <- removeTerm lhs
  rhs' <- removeTerm rhs
  Just $ App lhs' rhs'
removeTerm TType = Just TType
removeTerm Erased = Just Erased

{-
removeNTerm : {inner, xs, outer : _} ->
  Term (inner ++ xs ++ outer) -> Maybe (Term (inner ++ outer))
removeNTerm {xs=[]} tm = Just tm
removeNTerm {xs=[x]} tm = removeTerm tm
removeNTerm {xs=x::ys} tm = do
  tm2 <- removeTerm {outer=ys++outer} tm
  removeNTerm {xs=ys} tm2
-}

-- Term Contraction

contractVar : {x, outer : _} -> Var (x :: outer) -> Maybe (Var outer)
contractVar = removeVar {inner=[]}

contractNVar : {xs, outer : _} -> Var (xs ++ outer) -> Maybe (Var outer)
contractNVar {xs=[]} var = Just var
contractNVar {xs=x::ys} var = do
  var2 <- removeVar {inner=[]} {outer=ys ++ outer} var
  contractNVar {xs=ys} {outer=outer} var2

contractTerm : {x, outer : _} -> Term (x :: outer) -> Maybe (Term outer)
contractTerm = removeTerm {inner=[]}

contractNTerm : {xs, outer : _} -> Term (xs ++ outer) -> Maybe (Term outer)
contractNTerm {xs=[]} tm = Just tm
contractNTerm {xs=x::ys} tm = do
  tm2 <- removeTerm {inner=[]} {outer=ys ++ outer} tm
  contractNTerm {xs=ys} {outer=outer} tm2

-- Term Substitution

substTerm : {x, outer : _} -> Term outer -> Term (x :: outer) -> Term outer
substTerm tm tm2 = fromMaybe (Delay tm) (contractTerm tm2)

-- Term Inserting

insertVar : {inner, x, outer : _} ->
  Var (inner ++ outer) -> Var (inner ++ x :: outer)
insertVar {inner = []} (MkVar p) = MkVar (Later p)
insertVar {inner = (a :: as)} (MkVar First) = MkVar First
insertVar {inner = (a :: as)} (MkVar (Later p)) = 
  let MkVar p' = insertVar (MkVar p) in
  MkVar (Later p')

insertTerm : {inner, x, outer : _} ->
  Term (inner ++ outer) -> Term (inner ++ x :: outer)

insertBinder : {inner, x, outer : _} ->
  (Binder (Term (inner ++ outer))) -> (Binder (Term (inner ++ x :: outer)))

insertTerm (Local idx p) =
  let MkVar {i=idx'} p' = insertVar (MkVar p) in
  Local idx' p'
insertTerm (Ref ty n) = Ref ty n
insertTerm (Meta n xs) = Meta n (map insertTerm xs)
insertTerm (Bind nm bd scope) = 
  let bd' = insertBinder bd
      scope' = insertTerm {inner=nm::inner} scope
  in Bind nm bd' scope'
insertTerm (App lhs rhs) = App (insertTerm lhs) (insertTerm rhs)
insertTerm TType = TType
insertTerm Erased = Erased

insertBinder (Lam info ty) = Lam info (insertTerm ty)
insertBinder (Pi info ty) = Pi info (insertTerm ty)
insertBinder (PVar ty) = PVar (insertTerm ty)
insertBinder (PVTy ty) = PVTy (insertTerm ty)

-- Term weakening

weakenVar : {x, outer : _} -> Var outer -> Var (x :: outer)
weakenVar = insertVar {inner=[]}

weakenNVar : {xs, outer : _} -> Var (outer) -> Var (xs ++ outer)
weakenNVar {xs=[]} var = var
weakenNVar {xs=x::ys} var = let var' = weakenNVar {xs=ys} var in weakenVar var'

weakenTerm : {x, outer : _} -> Term outer -> Term (x :: outer)
weakenTerm = insertTerm {inner=[]}

weakenNTerm : {xs, outer : _} -> Term xs -> Term (outer ++ xs)
weakenNTerm {outer=[]} tm = tm
weakenNTerm {outer=x::ys} tm = let tm2 = weakenNTerm {outer=ys} tm in weakenTerm tm2

-- some help proofs

emptyConcatRight : {xs : List a} -> xs ++ [] = xs
emptyConcatRight {xs=[]} = Refl
emptyConcatRight {xs=x::ys} = cong (x::) (emptyConcatRight {xs=ys})

appendAssoc : (xs : List a) -> (ys : List a) -> (zs : List a) ->
              xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
appendAssoc [] ys zs = Refl
appendAssoc (x :: xs) ys zs = rewrite appendAssoc xs ys zs in Refl

-- Term Embedding

embedVar : {inner, x : _} -> Var inner -> Var (inner ++ [x])
embedVar var = do
  let var2 : Var (inner ++ []) = rewrite emptyConcatRight {xs=inner} in var
  insertVar {outer=[]} var2

embedNVar : {inner, xs : _} -> Var inner -> Var (inner ++ xs)
embedNVar {xs = []} var = rewrite emptyConcatRight {xs=inner} in var
embedNVar {xs = x::ys} var = 
  let var2 = embedNVar {xs=ys} var in
  insertVar {outer=ys} var2

embedTerm : {inner, x : _} -> Term inner -> Term (inner ++ [x])
embedTerm tm = do
  let tm2 : Term (inner ++ []) = rewrite emptyConcatRight {xs=inner} in tm
  insertTerm {outer=[]} tm2

embedNTerm : {inner, xs : _} -> Term inner -> Term (inner ++ xs)
embedNTerm {xs=[]} tm = rewrite emptyConcatRight {xs=inner} in tm
embedNTerm {xs=x::ys} tm = do
  let tm2 : Term (inner ++ []) = rewrite emptyConcatRight {xs=inner} in tm
  let tm3 : Term (inner ++ [x]) = insertTerm {outer=[]} tm2
  let tm4 : Term ((inner ++ [x]) ++ ys) = embedNTerm {inner=inner ++ [x]} {xs=ys} tm3
  let tm5 : Term (inner ++ x::ys) = rewrite appendAssoc {xs=inner} {ys=[x]} {zs=ys} in tm4
  tm5

public export
data CompatibleVars : List Name -> List Name -> Type where
     CompatPre : CompatibleVars xs xs
     CompatExt : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys

--- Show instances

export
getFnArgs : Term vars -> (Term vars, List (Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars ->
            (Term vars, List (Term vars))
    getFA args (App f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
Show Name where
  show (UN n) = n
  show (MN n i) = "{" ++ n ++ ":" ++ show i ++ "}"

export
nameAt : {vars : _} ->
         (idx : Nat) -> (0 p : IsVar n idx vars) -> Name
nameAt {vars = n :: ns} Z First = n
nameAt {vars = n :: ns} (S k) (Later p) = nameAt k p

-- why this tiny-idris source code doesn't compile? (not total)
{-
export 
{vars : _} -> Show (Term vars) where
  show tm = let (fn, args) = getFnArgs tm in showApp fn args
    where
      showApp : {vars : _} -> Term vars -> List (Term vars) -> String
      showApp (Local {name} idx p) []
         = show (nameAt idx p) ++ "[" ++ show idx ++ "]"
      showApp (Ref _ n) [] = show n
      showApp (Meta n args) []
          = "?" ++ show n ++ "_" ++ show args
      showApp (Bind x (Lam p ty) sc) []
          = "\\" ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (Pi Explicit ty) sc) []
          = "((" ++ show x ++ " : " ++ show ty ++
            ") -> " ++ show sc ++ ")"
      showApp (Bind x (Pi Implicit ty) sc) []
          = "{" ++ show x ++ " : " ++ show ty ++
            "} -> " ++ show sc
      showApp (Bind x (PVar ty) sc) []
          = "pat " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (PVTy ty) sc) []
          = "pty " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (App _ _) [] = "[can't happen]"
      showApp TType [] = "Type"
      showApp Erased [] = "[_]"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                        assert_total (showSep " " (map show args))
                     ++ ")"
-}