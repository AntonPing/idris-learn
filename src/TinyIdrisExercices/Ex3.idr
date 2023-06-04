
-- 1. Prove that appending Nil is the identity
-- (Note: this is defined in Data.List, but have a go yourself!)
appendNilNeutral : (xs : List a) -> xs ++ [] = xs
appendNilNeutral [] = Refl
appendNilNeutral (x :: xs) = rewrite appendNilNeutral xs in Refl

-- 2. Prove that appending lists is associative.
-- (Note: also defined in Data.List)
appendAssoc : (xs : List a) -> (ys : List a) -> (zs : List a) ->
              xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
appendAssoc [] ys zs = Refl
appendAssoc (x :: xs) ys zs = rewrite appendAssoc xs ys zs in Refl

-- A tree indexed by the (inorder) flattening of its contents
data Tree : List a -> Type where
     Leaf : Tree []
     Node : -- {0 a : Type} -> {0 xs : List a} -> {0 x : a} ->  {0 ys : List a} -> 
        Tree xs -> (x : a) -> Tree ys -> Tree (xs ++ x :: ys)



appendMoveIn : (x : a) -> (xs : List a) -> (ys : List a) -> 
               x :: (xs ++ ys) = (x :: xs) ++ ys
appendMoveIn x [] ys = Refl
appendMoveIn x (y :: xs) ys = Refl

{-
-- my first solution, pretty verbose
-- 3. Fill in rotateLemma. You'll need appendAssoc.
getTreeList : {0 xs : _} -> Tree xs -> (ys ** xs = ys)
getTreeList Leaf = ([] ** Refl)
getTreeList (Node left n right) = do
    let (lxs ** prf1) = getTreeList left
    let (rxs ** prf2) = getTreeList right
    rewrite prf1
    rewrite prf2
    (lxs ++ n :: rxs ** Refl)

rotateL : Tree zs -> Tree zs
rotateL Leaf = Leaf
rotateL (Node left n Leaf) = Node left n Leaf
rotateL (Node left n  (Node rightl n' rightr)) = do
    -- 1: (lxs ++ (n :: (rlxs ++ (n' :: rrxs))))
    -- 2: (lxs ++ ((n :: rlxs) ++ (n' :: rrxs))))
    -- 3: ((lxs ++ (n :: rlxs)) ++ (n' :: rrxs))
    let (lxs ** prf1) = getTreeList left
    let (rlxs ** prf2) = getTreeList rightl
    let (rrxs ** prf3) = getTreeList rightr
    rewrite prf1
    rewrite prf2
    rewrite prf3
    rewrite appendMoveIn n rlxs (n' :: rrxs)
    rewrite appendAssoc lxs (n :: rlxs) (n' :: rrxs)
    rewrite sym prf1
    rewrite sym prf2
    rewrite sym prf3
    Node (Node left n rightl) n' rightr
-}

-- my final solution, much better
-- 3. Fill in rotateLemma. You'll need appendAssoc.
rotateL : Tree zs -> Tree zs
rotateL Leaf = Leaf
rotateL (Node left n Leaf) = Node left n Leaf
rotateL (Node {xs} {ys = us ++ n' :: vs} left n  (Node {xs = us} {ys = vs} rightl n' rightr)) = do
    -- 1: (xs ++ (n :: (us ++ (n' :: vs))))
    -- 2: (xs ++ ((n ::  us) ++ (n' :: vs))))
    -- 3: ((xs ++ (n :: us)) ++ (n' :: vs))
    rewrite appendMoveIn n us (n' :: vs)
    rewrite appendAssoc xs (n :: us) (n' :: vs)
    Node (Node left n rightl) n' rightr

-- 4. Complete the definition of rotateR
rotateR : Tree xs -> Tree xs
