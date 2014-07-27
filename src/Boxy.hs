module FPH where

type Ident = String
data Expr = 
      Var Ident
    | Abs Ident Expr
    | App Expr Expr
    | Let Ident Expr
    -- and a few literals
    | EInt Integer
    | EBool Bool
    deriving Show

type VarID = Int
data MonoType =
      TypeVar VarID
    | FuncType Type Type
    | IntType
    | BoolType
    deriving Show
data NestedType = Mono MonoType | FuncType PolyType PolyType
data PolyType = ForAll [VarID] MonoType deriving Show

data Boxy a = Boxy a deriving Show
