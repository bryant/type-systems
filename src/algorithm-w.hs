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
type VarTypeMap = (Ident, PolyType)
type Context = [VarTypeMap]
data InfCtx = InfCtx { assumps :: [(Ident, PolyType)], id_gen :: TVarID }
    deriving Show
type IDGen = State.State TVarID

left_merge :: Eq a => [(a, b)] -> [(a, b)] -> [(a, b)]
left_merge = List.unionBy $ \x y -> fst x == fst y

-- (s1 `compose` s0) `s` tvar = s1 `s` (s0 `s` tvar)
compose :: Substs -> Substs -> Substs
compose s1 s0 = left_merge s0 s1'
    where s1' = flip map s1 $ \(x, y) -> (x, subst s0 y)

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

instance HasFree n => HasFree (a, n) where
    free_var = free_var . snd
    subst subs (var, forall) = (var, subst subs forall)

-- makes Context an instance of HasFree
instance HasFree n => HasFree [n] where
    -- left fold carries implicit nub
    free_var = List.foldl' List.union [] . map free_var
    subst s = map $ subst s

new_var :: IDGen TVarID
new_var = do
    vid <- State.get
    State.modify (+1)
    return vid

unify :: Type -> Type -> Substs
unify (TypeVar vid) u = unify u $ TypeVar vid
unify u (TypeVar vid)
    | u == TypeVar vid = []
    | vid `elem` free_var u = error $ "occurs check: " ++ show vid ++
                                      "occurs in " ++ show u
    | otherwise = [(vid, u)]
unify (FuncType t0 t1) (FuncType t0' t1') = s1 `compose` s0
    where (s0, s1) = (unify t0 t0', unify (subst s0 t1) (subst s0 t1'))
unify (ListType t) (ListType t') = unify t t'
unify t t'
    | t == t' = []
    | otherwise = error $ "cannot unify " ++ show t ++ " with " ++ show t'

infer :: Context -> Expr -> IDGen (Substs, Type)
infer ctx (Var binding) = case List.lookup binding ctx of
    Just (ForAll qvars monotype) -> do
        subs <- flip mapM qvars $ \qid -> do
            n <- new_var
            return (qid, TypeVar n)
        return ([], subst subs monotype)
    Nothing -> error $ "unknown variable: " ++ show binding

-- \x -> id x ==> Abs "x" (App (Var "id") (Var "x"))
-- infer {} Abs "x" (App (Var "id") (Var "x"))
-- >>> infer {x: forall. 1} (App (Var "id") (Var "x"))
-- >>> >>> infer {x: forall. 1} (Var "id")
-- >>> >>> >>> forall. 2 -> 2
-- >>> >>> unify (2 -> 2) (1 -> 3)
-- >>> >>> >>> unify 2 1
-- >>> >>> >>> >>> {1 ~ 2}
-- >>> >>> >>> unify 2 3
-- >>> >>> >>> >>> {3 ~ 2}
-- >>> >>> >>> {3 ~ 2, 1 ~ 2}
-- >>> >>> k
infer ctx (App e0 e1) = do
    (s0, fntype) <- infer ctx e0
    (s1, argtype) <- infer (subst s0 ctx) e1
    rettype <- TypeVar `fmap` new_var
    let s2 = unify (subst s1 fntype) $ FuncType argtype rettype
    return (s2 `compose` s1 `compose` s0, subst s2 rettype)

-- let id = \x -> x in id :: forall 1. 1 -> 1
-- let const = \x -> \y -> x in const :: forall 1 2. 1
-- Let "const" (Abs "x" (Abs "y" (Var "x"))) (Var "const")
infer ctx (Abs bind e) = do
    n <- TypeVar `fmap` new_var
    -- left_merge simulates name shadowing
    (s, t) <- flip infer e $ [(bind, ForAll [] n)] `left_merge` ctx
    return (s, FuncType (subst s n) t)

infer ctx (Let bind e0 e1) = do
    n <- TypeVar `fmap` new_var
    (s0, t0) <- flip infer e0 $ [(bind, ForAll [] n)] `left_merge` ctx
    let s1 = unify t0 $ subst s0 n
    let ctx' = subst (s1 `compose` s0) ctx
    let fv = free_var (subst s1 t0) List.\\ free_var ctx'
    (s2, t2) <- flip infer e1 $ [(bind, ForAll fv $ subst s1 t0)] `left_merge` ctx'
    return (s2 `compose` s1 `compose` s0, t2)

-- The rules of Algorithm W proper (implemented in `infer`) are technically
-- more stringent than the original set of Hindley-Milner (HM) rules. For
-- instance, HM would type `\x -> x` to be typed `forall a. a -> a`, while W
-- would be stuck at the monotype `forall. a -> a`, which technically makes no
-- sense at the top level.
w :: Context -> Expr -> IDGen (Substs, PolyType)
w ctx expr = do
    (s, t) <- infer ctx expr
    let fv = free_var t List.\\ free_var (subst s ctx)
    return (s, ForAll fv t)
