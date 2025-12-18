{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}

-- | Template Haskell utilities for deriving LogicType instances.
--
-- This module provides automatic derivation of 'LogicType' instances with
-- customizable quote strings and smart constructor names.
--
-- = Basic Usage
--
-- @
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE TemplateHaskell #-}
--
-- import Control.Applicative (empty, pure, (\<$\>), (\<*\>), (*\>))
-- import TypedRedex
-- import TypedRedex.Core.Internal.Logic (Logic(..), LogicType(..), Reified)
-- import TypedRedex.Interp.PrettyPrint (LogicVarNaming(..))
-- import TypedRedex.DSL.Type (quote0, quote1, quote2, quote3)
-- import TypedRedex.DSL.TH (deriveLogicType, (~>))
--
-- data Tm = Unit | Var Nat | Lam Ty Tm | App Tm Tm
--   deriving (Eq, Show)
--
-- deriveLogicType ''Tm
--   [ 'Unit ~> ("Unit", "unit'")
--   , 'Var  ~> ("Var", "var")
--   , 'Lam  ~> ("Lam", "lam")
--   , 'App  ~> ("App", "app")
--   ]
-- @
--
-- This generates:
--
-- 1. @instance LogicVarNaming Tm@ (using default naming)
-- 2. @instance LogicType Tm@ with:
--    - @data Reified Tm var = UnitR | VarR (Logic Nat var) | ...@
--    - All required methods (@project@, @reify@, @quote@, @unifyVal@, @derefVal@)
-- 3. Smart constructors: @unit' :: Logic Tm var@, @var :: Logic Nat var -> Logic Tm var@, etc.
--
-- = Custom Variable Naming
--
-- To use custom variable naming, define the 'LogicVarNaming' instance
-- /before/ the 'deriveLogicType' splice, which will skip generating it:
--
-- @
-- instance LogicVarNaming Tm where
--   varNaming = VarNaming "E" (\\i -> "e" ++ show i)
--
-- deriveLogicType ''Tm [...]
-- @
--
module TypedRedex.DSL.TH
  ( deriveLogicType
  , deriveLogicTypeNoNaming
  , (~>)
  , ConSpec
  ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Name, mkName, nameBase)
import Control.Monad (forM, when)

-- These need to be imported by the TH module to use '' syntax
-- We import them here just so the '' names resolve
import TypedRedex.Interp.PrettyPrint (LogicVarNaming)
import TypedRedex.Core.Internal.Logic (Logic(..), LogicType, Reified)
import Control.Applicative (empty, pure, (<$>), (<*>), (*>))
import Data.Maybe (Maybe(..))

-- | Specification for a single constructor: (quote string, builder name)
type ConSpec = (Name, (String, String))

-- | Associate a constructor with its quote string and builder name.
--
-- @'MyConstructor ~> ("QuoteName", "builderName")@
(~>) :: Name -> (String, String) -> ConSpec
(~>) = (,)

infixr 0 ~>

-- | Derive LogicType instance with custom naming.
-- Also generates a default LogicVarNaming instance.
--
-- Takes a type name and a list of constructor specifications.
-- Each specification maps a constructor to its (quote string, builder name).
--
-- If a constructor is not in the list, it uses the constructor name for both.
deriveLogicType :: Name -> [ConSpec] -> Q [Dec]
deriveLogicType typeName specs = do
  info <- reify typeName
  case info of
    TyConI (DataD _ _ tvs _ cons _) -> do
      when (not (null tvs)) $
        fail "deriveLogicType: type must not have type variables"
      deriveAll True typeName cons specs
    TyConI (NewtypeD _ _ tvs _ con _) -> do
      when (not (null tvs)) $
        fail "deriveLogicType: type must not have type variables"
      deriveAll True typeName [con] specs
    _ -> fail "deriveLogicType: expected a data or newtype declaration"

-- | Derive LogicType instance without generating LogicVarNaming.
-- Use this when you want to provide a custom LogicVarNaming instance.
deriveLogicTypeNoNaming :: Name -> [ConSpec] -> Q [Dec]
deriveLogicTypeNoNaming typeName specs = do
  info <- reify typeName
  case info of
    TyConI (DataD _ _ tvs _ cons _) -> do
      when (not (null tvs)) $
        fail "deriveLogicTypeNoNaming: type must not have type variables"
      deriveAll False typeName cons specs
    TyConI (NewtypeD _ _ tvs _ con _) -> do
      when (not (null tvs)) $
        fail "deriveLogicTypeNoNaming: type must not have type variables"
      deriveAll False typeName [con] specs
    _ -> fail "deriveLogicTypeNoNaming: expected a data or newtype declaration"

deriveAll :: Bool -> Name -> [Con] -> [ConSpec] -> Q [Dec]
deriveAll genNaming typeName cons specs = do
  let specMap = specs

  -- 1. Generate LogicVarNaming instance (empty, uses default) if requested
  varNamingInst <- if genNaming
                   then deriveVarNaming typeName
                   else return []

  -- 2. Generate LogicType instance
  logicTypeInst <- deriveLogicTypeInst typeName cons specMap

  -- 3. Generate smart constructors
  builders <- deriveBuilders typeName cons specMap

  return $ varNamingInst ++ logicTypeInst ++ builders

-- | Generate empty LogicVarNaming instance (uses default)
deriveVarNaming :: Name -> Q [Dec]
deriveVarNaming typeName = do
  let instType = AppT (ConT ''LogicVarNaming) (ConT typeName)
  return [InstanceD Nothing [] instType []]

-- We need these names - using '' syntax to get the actual names
-- For class methods, we use mkName with unqualified names

-- | Generate the LogicType instance
deriveLogicTypeInst :: Name -> [Con] -> [ConSpec] -> Q [Dec]
deriveLogicTypeInst typeName cons specMap = do
  varName <- newName "var"
  let varT = VarT varName

  -- Generate Reified data family instance
  reifiedCons <- mapM (genReifiedCon varT) cons
  let reifiedDec = DataInstD [] Nothing
        (AppT (AppT (ConT ''Reified) (ConT typeName)) varT)
        Nothing reifiedCons []

  -- Generate project method
  projectDec <- genProject cons

  -- Generate reify method
  reifyDec <- genReify cons

  -- Generate quote method
  quoteDec <- genQuote cons specMap

  -- Generate unifyVal method
  unifyValDec <- genUnifyVal cons

  -- Generate derefVal method
  derefValDec <- genDerefVal cons

  let instType = AppT (ConT ''LogicType) (ConT typeName)
  return [InstanceD Nothing [] instType
    [reifiedDec, projectDec, reifyDec, quoteDec, unifyValDec, derefValDec]]

-- | Generate a Reified constructor from an original constructor
genReifiedCon :: Type -> Con -> Q Con
genReifiedCon varT con = case con of
  NormalC name fields -> do
    let rName = mkName (nameBase name ++ "R")
    rFields <- mapM (wrapFieldType varT) fields
    return $ NormalC rName rFields
  RecC name fields -> do
    let rName = mkName (nameBase name ++ "R")
    rFields <- mapM (wrapRecFieldType varT) fields
    return $ RecC rName rFields
  _ -> fail "deriveLogicType: unsupported constructor form"

wrapFieldType :: Type -> BangType -> Q BangType
wrapFieldType varT (bang, ty) = do
  let wrappedTy = AppT (AppT (ConT ''Logic) ty) varT
  return (bang, wrappedTy)

wrapRecFieldType :: Type -> VarBangType -> Q VarBangType
wrapRecFieldType varT (name, bang, ty) = do
  let wrappedTy = AppT (AppT (ConT ''Logic) ty) varT
  return (name, bang, wrappedTy)

-- | Generate project method (unqualified name for class method)
genProject :: [Con] -> Q Dec
genProject cons = do
  clauses <- mapM genProjectClause cons
  return $ FunD (mkName "project") clauses

genProjectClause :: Con -> Q Clause
genProjectClause con = case con of
  NormalC name fields -> do
    let arity = length fields
    varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
    let pat = ConP name [] (map VarP varNames)
    let rName = mkName (nameBase name ++ "R")
    let body = foldl AppE (ConE rName)
                 [AppE (ConE 'Ground) (AppE (VarE (mkName "project")) (VarE v)) | v <- varNames]
    return $ Clause [pat] (NormalB body) []
  RecC name fields -> do
    let arity = length fields
    varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
    let pat = ConP name [] (map VarP varNames)
    let rName = mkName (nameBase name ++ "R")
    let body = foldl AppE (ConE rName)
                 [AppE (ConE 'Ground) (AppE (VarE (mkName "project")) (VarE v)) | v <- varNames]
    return $ Clause [pat] (NormalB body) []
  _ -> fail "deriveLogicType: unsupported constructor form"

-- | Generate reify method
genReify :: [Con] -> Q Dec
genReify cons = do
  clauses <- mapM genReifyClause cons
  let fallbackClause = Clause [WildP] (NormalB (ConE 'Nothing)) []
  return $ FunD (mkName "reify") (clauses ++ [fallbackClause])

genReifyClause :: Con -> Q Clause
genReifyClause con = case con of
  NormalC name fields -> do
    let arity = length fields
        rName = mkName (nameBase name ++ "R")
    if arity == 0
      then do
        let pat = ConP rName [] []
        let body = AppE (ConE 'Just) (ConE name)
        return $ Clause [pat] (NormalB body) []
      else do
        varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
        -- Pattern: ConR (Ground x1) (Ground x2) ...
        let pat = ConP rName [] [ConP 'Ground [] [VarP v] | v <- varNames]
        -- Body: Con <$> reify x1 <*> reify x2 <*> ...
        let reifyExprs = [AppE (VarE (mkName "reify")) (VarE v) | v <- varNames]
        let firstExpr = InfixE (Just (ConE name)) (VarE '(<$>)) (Just (head reifyExprs))
        let body = if arity == 1
                   then firstExpr
                   else foldl (\acc e -> InfixE (Just acc) (VarE '(<*>)) (Just e))
                              firstExpr (tail reifyExprs)
        return $ Clause [pat] (NormalB body) []
  RecC name fields -> genReifyClause (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveLogicType: unsupported constructor form"

-- | Generate quote method
genQuote :: [Con] -> [ConSpec] -> Q Dec
genQuote cons specMap = do
  clauses <- mapM (genQuoteClause specMap) cons
  return $ FunD (mkName "quote") clauses

genQuoteClause :: [ConSpec] -> Con -> Q Clause
genQuoteClause specMap con = case con of
  NormalC name fields -> do
    let arity = length fields
        rName = mkName (nameBase name ++ "R")
        qName = getQuoteName specMap name
    varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
    let pat = ConP rName [] (map VarP varNames)
    -- Use quote0, quote1, quote2, quote3 based on arity
    let quoteFn = case arity of
          0 -> mkName "quote0"
          1 -> mkName "quote1"
          2 -> mkName "quote2"
          3 -> mkName "quote3"
          _ -> error $ "deriveLogicType: constructor " ++ nameBase name ++ " has too many fields (max 3)"
    let body = foldl AppE (VarE quoteFn)
                 ([LitE (StringL qName), ConE rName] ++ map VarE varNames)
    return $ Clause [pat] (NormalB body) []
  RecC name fields -> genQuoteClause specMap (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveLogicType: unsupported constructor form"

getQuoteName :: [ConSpec] -> Name -> String
getQuoteName specMap name =
  case lookup name specMap of
    Just (qname, _) -> qname
    Nothing -> nameBase name

getBuilderName :: [ConSpec] -> Name -> String
getBuilderName specMap name =
  case lookup name specMap of
    Just (_, bname) -> bname
    Nothing -> lowerFirst (nameBase name)
  where
    lowerFirst [] = []
    lowerFirst (c:cs) = toLower c : cs
    toLower c | c >= 'A' && c <= 'Z' = toEnum (fromEnum c + 32)
              | otherwise = c

-- | Generate unifyVal method
genUnifyVal :: [Con] -> Q Dec
genUnifyVal cons = do
  unifName <- newName "unif"
  clauses <- mapM (genUnifyValClause unifName) cons
  let fallbackClause = Clause [WildP, WildP, WildP] (NormalB (VarE 'empty)) []
  return $ FunD (mkName "unifyVal") (clauses ++ [fallbackClause])

genUnifyValClause :: Name -> Con -> Q Clause
genUnifyValClause unifName con = case con of
  NormalC name fields -> do
    let arity = length fields
        rName = mkName (nameBase name ++ "R")
    if arity == 0
      then do
        let pat1 = ConP rName [] []
        let pat2 = ConP rName [] []
        let body = AppE (VarE 'pure) (TupE [])
        return $ Clause [VarP unifName, pat1, pat2] (NormalB body) []
      else do
        xNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
        yNames <- mapM (\i -> newName ("y" ++ show i)) [1..arity]
        let pat1 = ConP rName [] (map VarP xNames)
        let pat2 = ConP rName [] (map VarP yNames)
        -- unif x1 y1 *> unif x2 y2 *> ...
        let unifCalls = [foldl AppE (VarE unifName) [VarE x, VarE y] | (x, y) <- zip xNames yNames]
        let body = foldl1 (\acc e -> InfixE (Just acc) (VarE '(*>)) (Just e)) unifCalls
        return $ Clause [VarP unifName, pat1, pat2] (NormalB body) []
  RecC name fields -> genUnifyValClause unifName (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveLogicType: unsupported constructor form"

-- | Generate derefVal method
genDerefVal :: [Con] -> Q Dec
genDerefVal cons = do
  derefName <- newName "deref"
  clauses <- mapM (genDerefValClause derefName) cons
  return $ FunD (mkName "derefVal") clauses

genDerefValClause :: Name -> Con -> Q Clause
genDerefValClause derefName con = case con of
  NormalC name fields -> do
    let arity = length fields
        rName = mkName (nameBase name ++ "R")
    if arity == 0
      then do
        let pat = ConP rName [] []
        let body = AppE (VarE 'pure) (ConE name)
        return $ Clause [VarP derefName, pat] (NormalB body) []
      else do
        varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
        let pat = ConP rName [] (map VarP varNames)
        -- Con <$> deref x1 <*> deref x2 <*> ...
        let derefExprs = [AppE (VarE derefName) (VarE v) | v <- varNames]
        let firstExpr = InfixE (Just (ConE name)) (VarE '(<$>)) (Just (head derefExprs))
        let body = if arity == 1
                   then firstExpr
                   else foldl (\acc e -> InfixE (Just acc) (VarE '(<*>)) (Just e))
                              firstExpr (tail derefExprs)
        return $ Clause [VarP derefName, pat] (NormalB body) []
  RecC name fields -> genDerefValClause derefName (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveLogicType: unsupported constructor form"

-- | Generate smart constructors
deriveBuilders :: Name -> [Con] -> [ConSpec] -> Q [Dec]
deriveBuilders typeName cons specMap = concat <$> mapM (genBuilder typeName specMap) cons

genBuilder :: Name -> [ConSpec] -> Con -> Q [Dec]
genBuilder typeName specMap con = case con of
  NormalC name fields -> do
    let arity = length fields
        builderName = mkName (getBuilderName specMap name)
        rName = mkName (nameBase name ++ "R")

    varName <- newName "var"
    let varT = VarT varName

    -- Build the type signature
    argTypes <- forM fields $ \(_, ty) -> do
      return $ AppT (AppT (ConT ''Logic) ty) varT
    let resultType = AppT (AppT (ConT ''Logic) (ConT typeName)) varT
    let fullType = foldr (\a b -> AppT (AppT ArrowT a) b) resultType argTypes
    let sigType = ForallT [PlainTV varName SpecifiedSpec] [] fullType
    let sigDec = SigD builderName sigType

    -- Build the function body
    argNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
    let body = if arity == 0
               then AppE (ConE 'Ground) (ConE rName)
               else AppE (ConE 'Ground) (foldl AppE (ConE rName) (map VarE argNames))
    let funDec = FunD builderName [Clause (map VarP argNames) (NormalB body) []]

    return [sigDec, funDec]

  RecC name fields -> genBuilder typeName specMap (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveLogicType: unsupported constructor form"
