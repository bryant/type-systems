import qualified Data.List as List
import qualified Control.Monad.State as State

type Ident = String
type TVarID = Int

data Expr = Var Ident | App Expr Expr | Abs Ident Expr | Let Ident Expr Expr
data Type =
      TypeVar TVarID
    | TypeCtor Ident Int  -- number of type params
    | TypeApp Type [Type]
    deriving (Show, Eq)
data PolyType = ForAll [TVarID] Type deriving Show

data Subst = TVarID :==> Type deriving Show
data InfCtx = InfCtx { assumps :: [(Ident, PolyType)], id_gen :: TVarID }
    deriving Show
type Infer = State.State InfCtx

class HasFree t where
    free_var :: t -> [TVarID]
    substitute :: Subst -> t -> t

instance HasFree Type where
    free_var (TypeVar var) = [var]
    free_var (TypeApp ctor tyargs) =
        free_var ctor `List.union` concatMap free_var tyargs
    free_var _ = []

    substitute (tv :==> ty) t@(TypeVar tv')
        | tv == tv' = ty
        | otherwise = t
    substitute s (TypeApp ctor tyargs) = TypeApp ctor' tyargs'
        where
        ctor' = substitute s ctor
        tyargs' = flip map tyargs $ substitute s
    substitute _ t = t

instance HasFree PolyType where
    free_var (ForAll tvars monotype) = free_var monotype List.\\ tvars
    substitute s@(tv :==> ty) (ForAll tvars mono) = ForAll tvars' mono'
        where
        tvars' = List.delete tv tvars
        mono' = substitute s mono

-- hindley milner requires (->)
func_type = TypeCtor "(->)" 2
uint = TypeCtor "uint" 0
empty_ctx = InfCtx { assumps = [], id_gen = 0 }

new_var :: Infer TVarID
new_var = do
    vid <- id_gen `fmap` State.get
    State.modify inc_gen
    return vid
    where
    inc_gen ctx = ctx { id_gen = id_gen ctx + 1 }

instantiate :: PolyType -> Infer PolyType
instantiate (ForAll qvars mono) = do
    newqvars <- mapM (const new_var) qvars
    let subs = zipWith (:==>) qvars $ map TypeVar newqvars
    let newmono = List.foldl' (flip substitute) mono subs
    return $ ForAll newqvars newmono

unify :: Type -> Type -> [Subst]
unify (TypeVar vid) u = [vid :==> u]
unify u (TypeVar vid) = [vid :==> u]
unify (TypeApp u tyargs) (TypeApp u' tyargs')
    | u == u' = concat $ zipWith unify tyargs tyargs'
unify t t' = error $ "cannot unify " ++ show t ++ " with " ++ show t'

infer :: Expr -> Infer Type
infer (Var varname) = do
    a <- assumps `fmap` State.get
    case List.lookup varname a of
        Nothing -> error "unknown variable"
        Just ty -> return ty
infer (App expr0 expr1) = do
    t0 <- infer expr0
    t1 <- infer expr1
    let subs = unify (TypeApp func_type [t0
