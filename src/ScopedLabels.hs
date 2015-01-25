module ScopedLabels where

import qualified Data.List as List
import Control.Monad.Trans.State (StateT, get, modify, runStateT)
import Control.Monad (liftM)
import Control.Applicative ((<*))

type Ident = String

-- | Our AST.
data Expr =
      Var Ident
    | App Expr Expr
    | Abs Ident Expr
    | Let Ident Expr Expr
    deriving Show

type VarID = Int

type VarGenT = StateT VarID

data Type
    = TypeVar VarID
    | FuncType Type Type
    | RowEmpty  -- ^ {}
    | RowExt String Type Type  -- ^ {l :: (a :: *) | r}
    deriving (Show, Eq)

data TypeScheme = ForAll [VarID] Type deriving Show

type Subst = (VarID, Type)

class HasFree t where
    free_vars :: t -> [VarID]
    subst :: [Subst] -> t -> t

instance HasFree Type where
    free_vars (TypeVar vid) = [vid]
    free_vars (FuncType t0 t1) = free_vars t0 `List.union` free_vars t1
    free_vars RowEmpty = []
    free_vars (RowExt _ ty r) = free_vars ty `List.union` free_vars r  -- ugh

    subst s tv@(TypeVar vid) = maybe tv id $ lookup vid s
    subst s (FuncType u v) = FuncType (subst s u) (subst s v)
    subst s RowEmpty = RowEmpty
    subst s (RowExt label t r) = RowExt label (subst s t) (subst s r)

instance HasFree n => HasFree (a, n) where
    free_vars (_, ty) = free_vars ty

    subst s (vid, ty) = (vid, subst s ty)

instance HasFree a => HasFree [a] where
    free_vars = List.nub . concatMap free_vars
    subst s = map (subst s)

left_merge :: Eq a => [(a, b)] -> [(a, b)] -> [(a, b)]
left_merge = List.unionBy $ \x y -> fst x == fst y

compose :: [Subst] -> [Subst] -> [Subst]
compose s1 s0 = s0 `left_merge` map (subst s0) s1

new_type_var :: Monad m => VarGenT m Type
new_type_var = liftM TypeVar get >>= \n -> modify (+1) >> return n

unify :: Monad m => Type -> Type -> VarGenT m [Subst]
unify (TypeVar u) v
    | TypeVar u == v = return []
    | u `notElem` free_vars v = return [(u, v)]
    | otherwise = error $ show u ++ " occurs in " ++ show v
unify u v@(TypeVar _) = unify v u
unify (FuncType a b) (FuncType c d) = do
    s0 <- unify a c
    s1 <- unify (subst s0 b) (subst s0 d)
    return $ s1 `compose` s0
unify RowEmpty RowEmpty = return []
unify (RowExt l t r) other = case find_label l other of
    Nothing -> case end_of other of
        RowEmpty -> error "can't expect me to unify {} with {...}"
        TypeVar otherend -> if TypeVar otherend == end_of r
            then error "common end, different inits"
            else do
                beta <- new_type_var
                gamma <- new_type_var
                let s0 = [(otherend, RowExt l gamma beta)]
                s1 <- unify gamma (subst s0 t)
                s2 <- unify beta (subst (compose s1 s0) r)
                return $ s2 `compose` s1 `compose` s0
    Just (RowExt _ t' r') -> do
        s1 <- unify t t'
        s2 <- unify (subst s1 r) (subst s1 r')
        return $ s2 `compose` s1
    where
    find_label label row@(RowExt l t r)
        | label == l = Just row
        | otherwise = case find_label label r of
            Nothing -> Nothing
            Just (RowExt l' t' r') -> Just . RowExt l' t' $ RowExt l t r'
    find_label label _ = Nothing

    end_of (RowExt _ _ r) = end_of r
    end_of r = r
unify u v = error $ "can't unify [" ++ show u ++ "] with [" ++ show v ++ "]"
