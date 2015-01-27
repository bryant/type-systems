{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import qualified Data.List as List
import qualified Control.Monad.State as State
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Trans as Trans
import Control.Monad (liftM)
import Control.Applicative (Applicative)

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

newtype TypeInfT m a = TypeInfT
    { unTypeInfT :: Except.ExceptT String (State.StateT TVarID m) a }
    deriving (Functor, Applicative, Monad, Except.MonadError String,
              State.MonadState TVarID)

instance Trans.MonadTrans TypeInfT where
    lift = TypeInfT . Trans.lift . Trans.lift

runTypeInfT :: TypeInfT m a -> TVarID -> m (Either String a, TVarID)
runTypeInfT tf tvid = State.runStateT (Except.runExceptT $ unTypeInfT tf) tvid

left_merge :: Eq a => [(a, b)] -> [(a, b)] -> [(a, b)]
left_merge = List.unionBy $ \x y -> fst x == fst y

-- (s1 `compose` s0) `s` tvar = s1 `s` (s0 `s` tvar)
compose :: Substs -> Substs -> Substs
compose s1 s0 = left_merge s0' s1
    where s0' = flip map s0 $ \(x, y) -> (x, subst s1 y)

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

new_var :: Monad m => TypeInfT m Type
new_var = do
    vid <- State.get
    State.modify (+1)
    return $ TypeVar vid

unify :: Monad m => Type -> Type -> TypeInfT m Substs
unify u (TypeVar vid)
    | u == TypeVar vid = return []
    | vid `elem` free_var u = Except.throwError $
        "occurs check: " ++ show vid ++ "occurs in " ++ show u
    | otherwise = return [(vid, u)]
unify (TypeVar vid) u = unify u $ TypeVar vid
unify (FuncType t0 t1) (FuncType t0' t1') = do
    s0 <- unify t0 t0'
    s1 <- unify (subst s0 t1) (subst s0 t1')
    return $ s1 `compose` s0
unify (ListType t) (ListType t') = unify t t'
unify t t'
    | t == t' = return []
    | otherwise = Except.throwError $
        "cannot unify " ++ show t ++ " with " ++ show t'

gen_over :: Type -> Context -> PolyType
gen_over ty ctx = ForAll free ty
    where free = free_var ty List.\\ free_var ctx

infer :: Monad m => Context -> Expr -> TypeInfT m (Substs, Type)
infer ctx (Var binding) = case List.lookup binding ctx of
    Just (ForAll qvars monotype) -> do
        subs <- flip mapM qvars $ \qid -> do
            n <- new_var
            return (qid, n)
        return ([], subst subs monotype)
    Nothing -> Except.throwError $ "unknown variable: " ++ show binding
infer ctx (App e0 e1) = do
    (s0, fntype) <- infer ctx e0
    (s1, argtype) <- infer (subst s0 ctx) e1
    rettype <- new_var
    s2 <- unify (subst s1 fntype) $ FuncType argtype rettype
    return (s2 `compose` s1 `compose` s0, subst s2 rettype)
infer ctx (Abs bind e) = do
    n <- new_var
    -- left_merge simulates name shadowing
    (s, t) <- flip infer e $ [(bind, ForAll [] n)] `left_merge` ctx
    return (s, FuncType (subst s n) t)
infer ctx (Let bind e0 e1) = do
    (s0, t0) <- flip infer e0 ctx
    let ctx' = subst s0 ctx
    let sigma = t0 `gen_over` ctx'
    (s2, t2) <- flip infer e1 $ [(bind, sigma)] `left_merge` ctx'
    return (s2 `compose` s0, t2)

-- The rules of Algorithm W proper (implemented in `infer`) are technically
-- more stringent than the original set of Hindley-Milner (HM) rules. For
-- instance, HM would type `\x -> x` to be typed `forall a. a -> a`, while W
-- would be stuck at the monotype `forall. a -> a`, which technically makes no
-- sense at the top level.
w :: Monad m => Context -> Expr -> TypeInfT m (Substs, PolyType)
w ctx expr = do
    (s, t) <- infer ctx expr
    return (s, t `gen_over` subst s ctx)
