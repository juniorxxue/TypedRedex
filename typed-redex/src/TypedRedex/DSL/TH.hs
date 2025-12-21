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
--   [ 'Unit ~> ("Unit", "unit")
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
-- 3. Moded constructors: @unit :: T \'[] Tm rel@, @var :: T vs Nat rel -> T vs Tm rel@, etc.
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
    -- * Nominal Derivations
  , derivePermute
  , deriveHash
  , deriveSubst
  , SubstHook
  ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Name, mkName, nameBase)
import Control.Monad (when, forM)
import Data.Map (Map)
import qualified Data.Map as Map

-- These need to be imported by the TH module to use '' syntax
-- We import them here just so the '' names resolve
import TypedRedex.Interp.PrettyPrint (LogicVarNaming)
import TypedRedex.Core.Internal.Logic (Logic(..), LogicType, Reified)
import TypedRedex.DSL.Moded (T(..), ground, lift1, lift2, lift3, Union)
import TypedRedex.Nominal.Bind (Bind(..), Permute(..))
import TypedRedex.Nominal.Hash (Hash(..))
import TypedRedex.Nominal.Subst (Subst(..), substBind)
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

-- | Generate moded constructors (inlines raw constructor logic)
deriveBuilders :: Name -> [Con] -> [ConSpec] -> Q [Dec]
deriveBuilders typeName cons specMap = concat <$> mapM (genModedBuilder typeName specMap) cons

-- | Generate a moded constructor with inlined raw logic
genModedBuilder :: Name -> [ConSpec] -> Con -> Q [Dec]
genModedBuilder typeName specMap con = case con of
  NormalC name fields -> do
    let arity = length fields
        rName = mkName (nameBase name ++ "R")
        modedName = mkName (getBuilderName specMap name)

    relName <- newName "rel"
    let relT = VarT relName

    case arity of
      0 -> do
        -- Type: T '[] TypeName rel
        let resultT = AppT (AppT (AppT (ConT ''T) PromotedNilT) (ConT typeName)) relT
        let sigType = ForallT [PlainTV relName SpecifiedSpec] [] resultT
        let sigDec = SigD modedName sigType
        -- Body: ground (Ground ConR)
        let rawExpr = AppE (ConE 'Ground) (ConE rName)
        let body = AppE (VarE 'ground) rawExpr
        let funDec = FunD modedName [Clause [] (NormalB body) []]
        return [sigDec, funDec]

      1 -> do
        -- Type: T vs A rel -> T vs TypeName rel
        vsName <- newName "vs"
        let vsT = VarT vsName
        let (_, argTy) = head fields
        let argT = AppT (AppT (AppT (ConT ''T) vsT) argTy) relT
        let resultT = AppT (AppT (AppT (ConT ''T) vsT) (ConT typeName)) relT
        let fullType = AppT (AppT ArrowT argT) resultT
        let sigType = ForallT [PlainTV vsName SpecifiedSpec, PlainTV relName SpecifiedSpec] [] fullType
        let sigDec = SigD modedName sigType
        -- Body: lift1 (\x -> Ground (ConR x))
        xName <- newName "x"
        let rawExpr = AppE (ConE 'Ground) (AppE (ConE rName) (VarE xName))
        let lambda = LamE [VarP xName] rawExpr
        let body = AppE (VarE 'lift1) lambda
        let funDec = FunD modedName [Clause [] (NormalB body) []]
        return [sigDec, funDec]

      2 -> do
        -- Type: T vs1 A rel -> T vs2 B rel -> T (Union vs1 vs2) TypeName rel
        vs1Name <- newName "vs1"
        vs2Name <- newName "vs2"
        let vs1T = VarT vs1Name
            vs2T = VarT vs2Name
        let [(_, ty1), (_, ty2)] = fields
        let arg1T = AppT (AppT (AppT (ConT ''T) vs1T) ty1) relT
            arg2T = AppT (AppT (AppT (ConT ''T) vs2T) ty2) relT
            unionT = AppT (AppT (ConT ''Union) vs1T) vs2T
            resultT = AppT (AppT (AppT (ConT ''T) unionT) (ConT typeName)) relT
        let fullType = AppT (AppT ArrowT arg1T) (AppT (AppT ArrowT arg2T) resultT)
        let sigType = ForallT [PlainTV vs1Name SpecifiedSpec, PlainTV vs2Name SpecifiedSpec, PlainTV relName SpecifiedSpec] [] fullType
        let sigDec = SigD modedName sigType
        -- Body: lift2 (\x y -> Ground (ConR x y))
        xName <- newName "x"
        yName <- newName "y"
        let rawExpr = AppE (ConE 'Ground) (foldl AppE (ConE rName) [VarE xName, VarE yName])
        let lambda = LamE [VarP xName, VarP yName] rawExpr
        let body = AppE (VarE 'lift2) lambda
        let funDec = FunD modedName [Clause [] (NormalB body) []]
        return [sigDec, funDec]

      3 -> do
        -- Type: T vs1 A rel -> T vs2 B rel -> T vs3 C rel -> T (Union vs1 (Union vs2 vs3)) TypeName rel
        vs1Name <- newName "vs1"
        vs2Name <- newName "vs2"
        vs3Name <- newName "vs3"
        let vs1T = VarT vs1Name
            vs2T = VarT vs2Name
            vs3T = VarT vs3Name
        let [(_, ty1), (_, ty2), (_, ty3)] = fields
        let arg1T = AppT (AppT (AppT (ConT ''T) vs1T) ty1) relT
            arg2T = AppT (AppT (AppT (ConT ''T) vs2T) ty2) relT
            arg3T = AppT (AppT (AppT (ConT ''T) vs3T) ty3) relT
            union23T = AppT (AppT (ConT ''Union) vs2T) vs3T
            unionT = AppT (AppT (ConT ''Union) vs1T) union23T
            resultT = AppT (AppT (AppT (ConT ''T) unionT) (ConT typeName)) relT
        let fullType = AppT (AppT ArrowT arg1T) (AppT (AppT ArrowT arg2T) (AppT (AppT ArrowT arg3T) resultT))
        let sigType = ForallT [PlainTV vs1Name SpecifiedSpec, PlainTV vs2Name SpecifiedSpec, PlainTV vs3Name SpecifiedSpec, PlainTV relName SpecifiedSpec] [] fullType
        let sigDec = SigD modedName sigType
        -- Body: lift3 (\x y z -> Ground (ConR x y z))
        xName <- newName "x"
        yName <- newName "y"
        zName <- newName "z"
        let rawExpr = AppE (ConE 'Ground) (foldl AppE (ConE rName) [VarE xName, VarE yName, VarE zName])
        let lambda = LamE [VarP xName, VarP yName, VarP zName] rawExpr
        let body = AppE (VarE 'lift3) lambda
        let funDec = FunD modedName [Clause [] (NormalB body) []]
        return [sigDec, funDec]

      _ -> fail $ "deriveLogicType: constructor " ++ nameBase name ++ " has too many fields (max 3)"

  RecC name fields -> genModedBuilder typeName specMap (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveLogicType: unsupported constructor form"

--------------------------------------------------------------------------------
-- Nominal Derivations: Permute, Hash, Subst
--------------------------------------------------------------------------------

-- | Derive Permute instances for a type.
--
-- Takes the data type name and a list of name types that OCCUR in the type.
-- For name types not in the list, generates an identity swap.
--
-- Usage:
--
-- @
-- derivePermute ''Ty [''TyNom]
-- -- Generates:
-- --   instance Permute TyNom Ty where swap a b = ... (structural)
-- --   instance Permute Nom Ty where swap _ _ x = x  (identity, implicit)
--
-- derivePermute ''Tm [''Nom, ''TyNom]
-- -- Generates structural swap for both Nom and TyNom
-- @
derivePermute :: Name -> [Name] -> Q [Dec]
derivePermute typeName occursNames = do
  info <- reify typeName
  case info of
    TyConI (DataD _ _ tvs _ cons _) -> do
      when (not (null tvs)) $
        fail "derivePermute: type must not have type variables"
      -- Generate instances for each name type that occurs
      concat <$> mapM (genPermuteInstance typeName cons) occursNames
    TyConI (NewtypeD _ _ tvs _ con _) -> do
      when (not (null tvs)) $
        fail "derivePermute: type must not have type variables"
      concat <$> mapM (genPermuteInstance typeName [con]) occursNames
    _ -> fail "derivePermute: expected a data or newtype declaration"

-- | Generate a single Permute instance
genPermuteInstance :: Name -> [Con] -> Name -> Q [Dec]
genPermuteInstance typeName cons nameType = do
  aName <- newName "a"
  bName <- newName "b"
  clauses <- mapM (genPermuteClause nameType aName bName) cons
  let instType = AppT (AppT (ConT ''Permute) (ConT nameType)) (ConT typeName)
  let swapDec = FunD (mkName "swap") clauses
  return [InstanceD Nothing [] instType [swapDec]]

-- | Generate a clause for the swap function
genPermuteClause :: Name -> Name -> Name -> Con -> Q Clause
genPermuteClause nameType aName bName con = case con of
  NormalC conName fields -> do
    let arity = length fields
    varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
    let pat = ConP conName [] (map VarP varNames)
    -- For each field, apply swap recursively
    swappedFields <- forM (zip varNames fields) $ \(vn, (_, _)) -> do
      -- swap a b field
      return $ foldl AppE (VarE 'swap) [VarE aName, VarE bName, VarE vn]
    let body = foldl AppE (ConE conName) swappedFields
    return $ Clause [VarP aName, VarP bName, pat] (NormalB body) []
  RecC name fields -> genPermuteClause nameType aName bName (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "derivePermute: unsupported constructor form"

--------------------------------------------------------------------------------
-- Derive Hash
--------------------------------------------------------------------------------

-- | Derive Hash instances for a type.
--
-- Takes the data type name and a list of name types that can OCCUR in the type.
-- For name types not in the list, generates @occursIn _ _ = False@.
--
-- Automatically detects @Bind nameType body@ fields and adds shadowing logic.
--
-- Usage:
--
-- @
-- deriveHash ''Ty [''TyNom]
-- -- Generates:
-- --   instance Hash TyNom Ty where
-- --     occursIn a TUnit = False
-- --     occursIn a (TVar v) = a == v
-- --     occursIn a (TArr t1 t2) = occursIn a t1 || occursIn a t2
-- --     occursIn a (TAll (Bind b body))
-- --       | a == b = False  -- shadowed
-- --       | otherwise = occursIn a body
-- @
deriveHash :: Name -> [Name] -> Q [Dec]
deriveHash typeName occursNames = do
  info <- reify typeName
  case info of
    TyConI (DataD _ _ tvs _ cons _) -> do
      when (not (null tvs)) $
        fail "deriveHash: type must not have type variables"
      concat <$> mapM (genHashInstance typeName cons) occursNames
    TyConI (NewtypeD _ _ tvs _ con _) -> do
      when (not (null tvs)) $
        fail "deriveHash: type must not have type variables"
      concat <$> mapM (genHashInstance typeName [con]) occursNames
    _ -> fail "deriveHash: expected a data or newtype declaration"

-- | Generate a single Hash instance
genHashInstance :: Name -> [Con] -> Name -> Q [Dec]
genHashInstance typeName cons nameType = do
  aName <- newName "a"
  clauses <- mapM (genHashClause nameType aName) cons
  let instType = AppT (AppT (ConT ''Hash) (ConT nameType)) (ConT typeName)
  let occursInDec = FunD (mkName "occursIn") clauses
  return [InstanceD Nothing [] instType [occursInDec]]

-- | Generate a clause for the occursIn function
genHashClause :: Name -> Name -> Con -> Q Clause
genHashClause nameType aName con = case con of
  NormalC conName fields -> do
    let arity = length fields
    if arity == 0
      then do
        let pat = ConP conName [] []
        let body = ConE 'False
        return $ Clause [VarP aName, pat] (NormalB body) []
      else do
        varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
        let pat = ConP conName [] (map VarP varNames)
        -- Check each field - detect Bind for shadowing
        bodyExpr <- genHashBodyExpr nameType aName (zip varNames fields)
        return $ Clause [VarP aName, pat] (NormalB bodyExpr) []
  RecC name fields -> genHashClause nameType aName (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveHash: unsupported constructor form"

-- | Generate the body expression for occursIn, handling Bind specially
genHashBodyExpr :: Name -> Name -> [(Name, BangType)] -> Q Exp
genHashBodyExpr nameType aName fields = do
  exprs <- mapM (genFieldOccursIn nameType aName) fields
  case exprs of
    [] -> return $ ConE 'False
    [e] -> return e
    _ -> return $ foldl1 (\acc e -> InfixE (Just acc) (VarE '(||)) (Just e)) exprs

-- | Generate occurrence check for a single field
-- For Bind nameType body, generate: if a == bound then False else occursIn a body
genFieldOccursIn :: Name -> Name -> (Name, BangType) -> Q Exp
genFieldOccursIn nameType aName (varName, (_, fieldTy)) = do
  -- Check if field is a Bind of the same name type
  case fieldTy of
    AppT (AppT (ConT bindName) boundNameTy) _ | bindName == ''Bind -> do
      -- Check if the bound name type matches the name type we're checking
      case boundNameTy of
        ConT boundNameType | boundNameType == nameType -> do
          -- This is a Bind that binds our name type - generate shadowing check
          -- Pattern: case varName of Bind b body -> if a == b then False else occursIn a body
          bName <- newName "b"
          bodyName <- newName "body"
          let bindPat = ConP 'Bind [] [VarP bName, VarP bodyName]
          let shadowed = ConE 'False
          let notShadowed = foldl AppE (VarE 'occursIn) [VarE aName, VarE bodyName]
          let guard1 = (NormalG (InfixE (Just (VarE aName)) (VarE '(==)) (Just (VarE bName))), shadowed)
          let guard2 = (NormalG (ConE 'True), notShadowed)
          return $ CaseE (VarE varName) [Match bindPat (GuardedB [guard1, guard2]) []]
        _ -> do
          -- Different name type binding - just recurse
          return $ foldl AppE (VarE 'occursIn) [VarE aName, VarE varName]
    _ -> do
      -- Regular field - just recurse
      return $ foldl AppE (VarE 'occursIn) [VarE aName, VarE varName]

--------------------------------------------------------------------------------
-- Derive Subst
--------------------------------------------------------------------------------

-- | Hook for custom substitution handling of specific constructors.
type SubstHook = (Name, Q Exp)

-- | Derive Subst instance for a type with optional custom handlers.
--
-- Takes:
-- - The data type name
-- - The name type to substitute for
-- - A list of constructor hooks (constructor name, handler expression)
--
-- For constructors without hooks, generates recursive substitution.
-- For variable constructors (field type matches name type), generates equality check.
--
-- Usage:
--
-- @
-- deriveSubst ''Ty ''TyNom
--   [ 'TAll ~> [| \\name repl bnd -> TAll (substBind name repl bnd) |]
--   ]
-- -- Generates:
-- --   instance Subst TyNom Ty where
-- --     subst name replacement TUnit = TUnit
-- --     subst name replacement (TVar v)
-- --       | v == name = replacement
-- --       | otherwise = TVar v
-- --     subst name replacement (TArr t1 t2) = TArr (subst name replacement t1) (subst name replacement t2)
-- --     subst name replacement (TAll bnd) = TAll (substBind name replacement bnd)  -- custom hook
-- @
deriveSubst :: Name -> Name -> [SubstHook] -> Q [Dec]
deriveSubst typeName nameType hooks = do
  info <- reify typeName
  case info of
    TyConI (DataD _ _ tvs _ cons _) -> do
      when (not (null tvs)) $
        fail "deriveSubst: type must not have type variables"
      genSubstInstance typeName nameType cons hooks
    TyConI (NewtypeD _ _ tvs _ con _) -> do
      when (not (null tvs)) $
        fail "deriveSubst: type must not have type variables"
      genSubstInstance typeName nameType [con] hooks
    _ -> fail "deriveSubst: expected a data or newtype declaration"

-- | Generate the Subst instance
genSubstInstance :: Name -> Name -> [Con] -> [SubstHook] -> Q [Dec]
genSubstInstance typeName nameType cons hooks = do
  let hookMap = Map.fromList hooks
  nameName <- newName "name"
  replName <- newName "replacement"
  tyName <- newName "ty"

  clauses <- mapM (genSubstClause typeName nameType hookMap nameName replName) cons
  let instType = AppT (AppT (ConT ''Subst) (ConT nameType)) (ConT typeName)
  let substDec = FunD (mkName "subst") clauses
  return [InstanceD Nothing [] instType [substDec]]

-- | Generate a clause for the subst function
genSubstClause :: Name -> Name -> Map Name (Q Exp) -> Name -> Name -> Con -> Q Clause
genSubstClause typeName nameType hookMap nameName replName con = case con of
  NormalC conName fields -> do
    -- Check if there's a hook for this constructor
    case Map.lookup conName hookMap of
      Just hookQ -> do
        -- Use the hook expression
        hook <- hookQ
        let arity = length fields
        varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
        let pat = ConP conName [] (map VarP varNames)
        -- Apply hook: hook name replacement x1 x2 ... (depending on arity)
        let body = foldl AppE hook ([VarE nameName, VarE replName] ++ map VarE varNames)
        return $ Clause [VarP nameName, VarP replName, pat] (NormalB body) []

      Nothing -> do
        -- Generate default substitution
        let arity = length fields
        if arity == 0
          then do
            let pat = ConP conName [] []
            let body = ConE conName
            return $ Clause [VarP nameName, VarP replName, pat] (NormalB body) []
          else do
            varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
            let pat = ConP conName [] (map VarP varNames)
            -- Check if this is a variable constructor (single field matching name type)
            if arity == 1 && isVarCon nameType (head fields)
              then do
                -- Generate: if v == name then replacement else ConName v
                let vn = head varNames
                let eq = InfixE (Just (VarE vn)) (VarE '(==)) (Just (VarE nameName))
                let thenE = VarE replName
                let elseE = AppE (ConE conName) (VarE vn)
                let guard1 = (NormalG eq, thenE)
                let guard2 = (NormalG (ConE 'True), elseE)
                return $ Clause [VarP nameName, VarP replName, pat] (GuardedB [guard1, guard2]) []
              else do
                -- Generate recursive substitution for each field
                substFields <- forM varNames $ \vn ->
                  return $ foldl AppE (VarE 'subst) [VarE nameName, VarE replName, VarE vn]
                let body = foldl AppE (ConE conName) substFields
                return $ Clause [VarP nameName, VarP replName, pat] (NormalB body) []

  RecC name fields -> genSubstClause typeName nameType hookMap nameName replName (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveSubst: unsupported constructor form"

-- | Check if a field type matches the name type (for variable constructors)
isVarCon :: Name -> BangType -> Bool
isVarCon nameType (_, ConT fieldTy) = fieldTy == nameType
isVarCon _ _ = False
