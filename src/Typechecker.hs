{-# language OverloadedStrings #-}
module Typechecker where

import Control.Monad.State (State, runState, get, gets, modify, state)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import AST (Type(..), Scheme(..), Exp(..), Lit(..))

showT :: Show a => a -> Text
showT = Text.pack . show

freeTypeVars :: Type -> Set Text
freeTypeVars ty = case ty of
 TVar var ->
   Set.singleton var
 TFun t1 t2 ->
   Set.union (freeTypeVars t1) (freeTypeVars t2)

applySubst :: Substitution -> Type -> Type
applySubst subst ty = case ty of
  TVar var ->
    fromMaybe ty (Map.lookup var subst)
  TFun t1 t2 ->
    TFun (applySubst subst t1) (applySubst subst t2)
  _ -> ty

freeTypeVarsScheme :: Scheme -> Set Text
freeTypeVarsScheme (Scheme vars t) =
  Set.difference (freeTypeVars t) (Set.fromList vars)

applySubstScheme :: Substitution -> Scheme -> Scheme
applySubstScheme subst (Scheme vars t) =
  Scheme vars (applySubst (foldr Map.delete subst vars) t)

type Substitution = Map Text Type

emptySubst :: Substitution
emptySubst = Map.empty

-- | This is much more subtle than it seems. TODO(Christoph) explain
-- why composition is much "simpler" in the math and gets complicated
-- if you always flatten into a single map (hint: invariant is that
-- you never need to use "fix" to apply a substitution)
composeSubst :: Substitution -> Substitution -> Substitution
composeSubst s1 s2 = Map.union (Map.map (applySubst s1) s2) s1

newtype Environment = Environment (Map Text Scheme)

remove :: Environment -> Text -> Environment
remove (Environment env) var = Environment (Map.delete var env)

freeTypeVarsEnv :: Environment -> Set Text
freeTypeVarsEnv (Environment env) = foldMap freeTypeVarsScheme (Map.elems env)

applySubstEnv :: Substitution -> Environment -> Environment
applySubstEnv subst (Environment env) = Environment (Map.map (applySubstScheme subst) env)

generalize :: Environment -> Type -> Scheme
generalize env t = Scheme vars t
  where
    vars = Set.toList (Set.difference (freeTypeVars t) (freeTypeVarsEnv env))

data TIState = TIState { tiSupply :: Int, tiSubst :: Substitution }
type TI a = ExceptT Text (State TIState) a

initTIState :: TIState
initTIState = TIState 0 Map.empty

runTI :: TI a -> (Either Text a, TIState)
runTI ti = runState (runExceptT ti) initTIState

newTyVar :: Text -> TI Type
newTyVar prefix = do
  state (\s ->
    ( TVar (prefix <> showT (tiSupply s))
    , s { tiSupply = tiSupply s + 1})
    )

instantiate :: Scheme -> TI Type
instantiate (Scheme vars ty) = do
  newVars <- traverse (\_ -> newTyVar "a") vars
  let subst = Map.fromList (zip vars newVars)
  pure (applySubst subst ty)

varBind :: Text -> Type -> TI Substitution
varBind var ty
  | ty == TVar var = pure emptySubst
  -- TODO(Christoph) better error message, remember what the occurs check is
  | Set.member var (freeTypeVars ty) = throwError "occurs check failed"
  | otherwise = pure (Map.singleton var ty)

unify :: Type -> Type -> TI Substitution
unify ty1 ty2 = case (ty1, ty2) of
  (TFun l r, TFun l' r') -> do
    s1 <- unify l l'
    s2 <- unify (applySubst s1 r) (applySubst s1 r')
    pure (s1 `composeSubst` s2)
  (TVar u, t) -> varBind u t
  (t, TVar u) -> varBind u t
  (t1, t2) -> throwError ("types do not unify: " <> showT t1 <> " vs. " <> showT t2)

inferLiteral :: Lit -> TI (Substitution, Type)
inferLiteral lit =
  pure (emptySubst, case lit of
    LInt _ -> TInt
    LBool _ -> TBool)

infer :: Environment -> Exp -> TI (Substitution, Type)
infer env@(Environment env') exp = case exp of
  EVar var -> case Map.lookup var env' of
    Nothing ->
      throwError ("unbound variable: " <> showT var)
    Just ty -> do
      -- TODO(Christoph) see if we need this without let generalization
      t <- instantiate ty
      pure (emptySubst, t)
  ELit lit ->
    inferLiteral lit
  EApp e0 e1 -> do
    tv <- newTyVar "u"
    (s0, t0) <- infer env e0
    (s1, t1) <- infer (applySubstEnv s0 env) e1
    s2 <- unify (applySubst s1 t0) (TFun t1 tv)
    pure (s2 `composeSubst` s1 `composeSubst` s0, applySubst s2 tv)
  EAbs n e -> do
    tv <- newTyVar "a"
    let tmpEnv = Environment (Map.insert n (Scheme [] tv) env')
    (s1, t1) <- infer tmpEnv e
    pure (s1, TFun (applySubst s1 tv) t1)
  exp ->
    throwError "not implemented"
