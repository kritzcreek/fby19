{-# language OverloadedStrings #-}
module Typechecker where

import Control.Monad (replicateM)
import Control.Monad.State (State, runState, get, put, gets, modify)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import AST (Type(..), Scheme(..), Exp(..), Lit(..), prettyType, prettyScheme)

import Debug.Trace

type Substitution = Map Text Type

emptySubst :: Substitution
emptySubst = Map.empty

applySubst :: Substitution -> Type -> Type
applySubst subst ty = case ty of
  TVar var ->
    fromMaybe (TVar var) (Map.lookup var subst)
  TFun arg res ->
    TFun (applySubst subst arg) (applySubst subst res)
  TInt -> TInt
  TBool -> TBool

applySubstScheme :: Substitution -> Scheme -> Scheme
applySubstScheme subst (Scheme vars t) =
  -- The fold takes care of name shadowing
  Scheme vars (applySubst (foldr Map.delete subst vars) t)

-- | This is much more subtle than it seems. (union is left biased)
--
composeSubst :: Substitution -> Substitution -> Substitution
composeSubst s1 s2 = Map.union (Map.map (applySubst s1) s2) s1

type TI a = ExceptT Text (State Int) a

runTI :: TI a -> (Either Text a, Int)
runTI ti = runState (runExceptT ti) 0

-- | Creates a fresh type variable
newTyVar :: TI Type
newTyVar = do
  s <- get
  put (s + 1)
  pure (TVar ("u" <> showT s))

freeTypeVars :: Type -> Set Text
freeTypeVars ty = case ty of
 TVar var ->
   Set.singleton var
 TFun t1 t2 ->
   Set.union (freeTypeVars t1) (freeTypeVars t2)
 _ ->
   Set.empty

freeTypeVarsScheme :: Scheme -> Set Text
freeTypeVarsScheme (Scheme vars t) =
  Set.difference (freeTypeVars t) (Set.fromList vars)

-- | Creates a fresh unification variable and binds it to the given type
varBind :: Text -> Type -> TI Substitution
varBind var ty
  | ty == TVar var = pure emptySubst
  | Set.member var (freeTypeVars ty) = throwError "occurs check failed"
  | otherwise = pure (Map.singleton var ty)

unify :: Type -> Type -> TI Substitution
unify TInt TInt = pure emptySubst
unify TBool TBool = pure emptySubst
unify (TFun l r) (TFun l' r') = do
  s1 <- unify l l'
  s2 <- unify (applySubst s1 r) (applySubst s1 r')
  pure (s1 `composeSubst` s2)
unify (TVar u) t = varBind u t
unify t (TVar u) = varBind u t
unify t1 t2 =
  throwError ("types do not unify: " <> showT t1 <> " vs. " <> showT t2)

type Context = Map Text Scheme

applySubstCtx :: Substitution -> Context -> Context
applySubstCtx subst ctx = Map.map (applySubstScheme subst) ctx

freeTypeVarsCtx :: Context -> Set Text
freeTypeVarsCtx ctx = foldMap freeTypeVarsScheme (Map.elems ctx)

generalize :: Context -> Type -> Scheme
generalize ctx t = Scheme vars t
  where
    vars = Set.toList (Set.difference (freeTypeVars t) (freeTypeVarsCtx ctx))

instantiate :: Scheme -> TI Type
instantiate (Scheme vars ty) = do
  newVars <- traverse (const newTyVar) vars
  let subst = Map.fromList (zip vars newVars)
  pure (applySubst subst ty)

inferLiteral :: Lit -> TI (Substitution, Type)
inferLiteral lit =
  pure (emptySubst, case lit of
    LInt _ -> TInt
    LBool _ -> TBool)

infer :: Context -> Exp -> TI (Substitution, Type)
infer ctx exp = case exp of
  EVar var -> case Map.lookup var ctx of
    Nothing ->
      throwError ("unbound variable: " <> showT var)
    Just ty -> do
      t <- instantiate ty
      pure (emptySubst, t)
  ELit lit ->
    inferLiteral lit
  EApp fun arg -> do
    tyRes <- newTyVar
    (s1, tyFun) <- infer ctx fun
    (s2, tyArg) <- infer (applySubstCtx s1 ctx) arg
    s3 <- unify (applySubst s2 tyFun) (TFun tyArg tyRes)
    pure (s3 `composeSubst` s2 `composeSubst` s1, applySubst s3 tyRes)
  ELam binder body -> do
    tyBinder <- newTyVar
    let tmpCtx = Map.insert binder (Scheme [] tyBinder) ctx
    (s1, tyBody) <- infer tmpCtx body
    pure (s1, TFun (applySubst s1 tyBinder) tyBody)
  ELet binder binding body -> do
    (s1, tyBinder) <- infer ctx binding
    -- let scheme = generalize ctx (applySubst s1 t1)
    let scheme = Scheme [] (applySubst s1 tyBinder)
    let tmpCtx = Map.insert binder scheme ctx
    (s2, tyBody) <- infer (applySubstCtx s1 tmpCtx) body
    pure (composeSubst s1 s2, tyBody)

typeInference :: Context -> Exp -> TI Type
typeInference ctx exp = do
  (s, t) <- infer ctx exp
  pure (applySubst s t)

primitives :: Context
primitives = Map.fromList
  [ ("identity", Scheme ["a"] (TFun (TVar "a") (TVar "a")))
  , ("const", Scheme ["a", "b"] (TFun (TVar "a") (TFun (TVar "b") (TVar "a"))))
  , ("add", Scheme [] (TFun TInt (TFun TInt TInt)))
  , ("gte", Scheme [] (TFun TInt (TFun TInt TBool)))
  , ("if", Scheme ["a"] (TFun TBool (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))))
  ]

testTI :: Exp -> IO ()
testTI e = do
  let (res, _) = runTI (typeInference primitives e)
  case res of
    Left err -> putStrLn $ show e ++ "\n " ++ Text.unpack err ++ "\n"
    Right t  -> putStrLn $ "\n" ++ Text.unpack (prettyScheme (generalize Map.empty t)) ++ "\n"

showT :: Show a => a -> Text
showT = Text.pack . show
