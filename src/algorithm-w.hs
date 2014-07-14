import qualified Data.List as List
import qualified Control.Monad.State as State

type Ident = String
type TVarID = Int

data Expr = Var Ident | App Expr Expr | Abs Ident Expr | Let Ident Expr Expr
data Type =
      TypeVar TVarID
    | FuncType Type Type
    | IntType
    | BoolType
    | ListType Type
    deriving (Show, Eq)
data PolyType = ForAll [TVarID] Type deriving Show

type Substs = [(TVarID, Type)]
type Context = [(Ident, PolyType)]
data InfCtx = InfCtx { assumps :: [(Ident, PolyType)], id_gen :: TVarID }
    deriving Show
type IDGen = State.State TVarID

each = flip map

-- (s1 `compose` s0) `s` tvar = s1 `s` (s0 `s` tvar)
compose :: Substs -> Substs -> Substs
compose s1 s0 = merge s0 s1'
    where
    s1' = each s1 $ \(x, y) -> (x, subst s0 y)
    merge = List.unionBy $ \x y -> fst x == fst y

class HasFree t where
    free_var :: t -> [TVarID]
    subst :: Substs -> t -> t

instance HasFree Type where
    free_var (TypeVar var) = [var]
    free_var (FuncType t0 t1) = free_var t0 `List.union` free_var t1
    free_var (ListType t) = free_var t
    free_var _ = []

    subst subs (TypeVar vid) = case List.lookup vid subs of
        Nothing -> TypeVar vid
        Just t -> t
    subst subs (FuncType t0 t1) = FuncType (subst subs t0) (subst subs t1)
    subst subs (ListType t) = ListType $ subst subs t
    subst _ t = t

instance HasFree PolyType where
    free_var (ForAll qvars monotype) = free_var monotype List.\\ qvars
    subst subs (ForAll qvars mono) = ForAll qvars' mono'
        where
        qvars' = qvars List.\\ map fst subs
        mono' = subst subs mono

new_var :: IDGen TVarID
new_var = do
    vid <- State.get
    State.modify (+1)
    return vid

unify :: Type -> Type -> Substs
unify (TypeVar vid) u = [(vid, u)]
unify u (TypeVar vid) = [(vid, u)]
unify (FuncType t0 t1) (FuncType t0' t1') = s1 `compose` s0
    where (s0, s1) = (unify t0 t0', unify (subst s0 t1) (subst s0 t1'))
unify (ListType t) (ListType t') = unify t t'
unify t t'
    | t == t' = []
    | otherwise = error $ "cannot unify " ++ show t ++ " with " ++ show t'

infer :: Context -> Expr -> IDGen PolyType
infer ctx (Var binding) = case List.lookup binding ctx of
    Just ty -> inst ty
    Nothing -> error $ "unknown variable: " ++ show binding
    where
    inst :: PolyType -> IDGen PolyType
    inst (ForAll qvars mono) = do
        newvars <- mapM (const new_var) qvars
        let subs = zipWith (\q v -> (q, TypeVar v)) qvars newvars
        return . ForAll newvars $ subst subs mono
infer ctx (App e0 e1) = undefined
infer ctx (Abs bind e1) = undefined
infer ctx (Let bind e0 e1) = undefined