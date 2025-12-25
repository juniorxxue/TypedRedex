{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}

-- | Template Haskell utilities for deriving LogicType instances.
--
-- This module provides automatic derivation of 'LogicType' instances with
-- smart constructor names for the moded DSL.
--
-- = Basic Usage
--
-- @
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE TemplateHaskell #-}
--
-- import TypedRedex
-- import TypedRedex.DSL.TH (deriveLogicType, (~>))
--
-- data Tm = Unit | Var Nat | Lam Ty Tm | App Tm Tm
--   deriving (Eq, Show)
--
-- deriveLogicType ''Tm
--   [ 'Unit ~> "unit"
--   , 'Var  ~> "var"
--   , 'Lam  ~> "lam"
--   , 'App  ~> "app"
--   ]
-- @
--
-- This generates:
--
-- 1. @instance LogicType Tm@ with:
--    - @data Reified Tm var = UnitR | VarR (Logic Nat var) | ...@
--    - All required methods (@project@, @reify@, @children@, @unifyVal@, @derefVal@)
-- 2. Moded constructors: @unit :: T '[] Tm rel@, @var :: T vs Nat rel -> T vs Tm rel@, etc.
--
-- Note: TypesetNaming and quote instances are NOT generated here.
-- Use the interpreter layer (typedredex-interp) for pretty-printing support.
module TypedRedex.DSL.TH
  ( deriveLogicType
  , (~>)
  , ConSpec
    -- * Nominal Derivations
  , derivePermute
  , deriveHash
  , deriveSubsto
  ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Name, mkName, nameBase)
import Control.Monad (when, forM)
import Data.Proxy (Proxy(..))

-- These need to be imported by the TH module to use '' syntax
import TypedRedex.Logic (Logic(..), LogicType(project, Reified), Reified, Field(..), Redex(..), RedexEval(..), RedexFresh(..), RedexHash(..))
import TypedRedex.DSL.Moded (T(..), ground, lift1, lift2, lift3, Union)
import TypedRedex.Nominal.Bind (Bind(..), Permute(..))
import TypedRedex.Nominal.Hash (Hash(..))
import TypedRedex.Nominal (bind)
import TypedRedex.Nominal.Subst (Substo(..))
import TypedRedex.DSL.Eval (eval)
import TypedRedex.DSL.Relation (conde, (<=>))
import TypedRedex.DSL.Fresh (LTerm, freshLogic, Freshable(..))
import Control.Applicative (empty, pure, (<$>), (<*>), (*>))
import Data.Maybe (Maybe(..))

-- | Specification for a single constructor: builder name
type ConSpec = (Name, String)

-- | Associate a constructor with its builder name.
--
-- @'MyConstructor ~> "builderName"@
(~>) :: Name -> String -> ConSpec
(~>) = (,)

infixr 0 ~>

-- | Derive LogicType instance.
--
-- Takes a type name and a list of constructor specifications.
-- Each specification maps a constructor to its builder name.
--
-- If a constructor is not in the list, it uses the lowercased constructor name.
deriveLogicType :: Name -> [ConSpec] -> Q [Dec]
deriveLogicType typeName specs = do
  info <- reify typeName
  case info of
    TyConI (DataD _ _ tvs _ cons _) -> do
      when (not (null tvs)) $
        fail "deriveLogicType: type must not have type variables"
      deriveAll typeName cons specs
    TyConI (NewtypeD _ _ tvs _ con _) -> do
      when (not (null tvs)) $
        fail "deriveLogicType: type must not have type variables"
      deriveAll typeName [con] specs
    _ -> fail "deriveLogicType: expected a data or newtype declaration"

deriveAll :: Name -> [Con] -> [ConSpec] -> Q [Dec]
deriveAll typeName cons specs = do
  -- 1. Generate LogicType instance
  logicTypeInst <- deriveLogicTypeInst typeName cons

  -- 2. Generate smart constructors
  builders <- deriveBuilders typeName cons specs

  return $ logicTypeInst ++ builders

-- | Generate the LogicType instance
deriveLogicTypeInst :: Name -> [Con] -> Q [Dec]
deriveLogicTypeInst typeName cons = do
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

  -- Generate children method
  childrenDec <- genChildren cons

  -- Generate quote method (for pretty-printing)
  quoteDec <- genQuote cons

  -- Generate unifyVal method
  unifyValDec <- genUnifyVal cons

  -- Generate derefVal method
  derefValDec <- genDerefVal cons

  let instType = AppT (ConT ''LogicType) (ConT typeName)
  return [InstanceD Nothing [] instType
    [reifiedDec, projectDec, reifyDec, childrenDec, quoteDec, unifyValDec, derefValDec]]

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

-- | Generate project method
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

-- | Generate children method (for occurs check / traversal)
genChildren :: [Con] -> Q Dec
genChildren cons = do
  clauses <- mapM genChildrenClause cons
  return $ FunD (mkName "children") clauses

genChildrenClause :: Con -> Q Clause
genChildrenClause con = case con of
  NormalC name fields -> do
    let arity = length fields
        rName = mkName (nameBase name ++ "R")
    varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
    let pat = ConP rName [] (map VarP varNames)
    -- Body: [Field Proxy x1, Field Proxy x2, ...]
    let fieldExprs = [AppE (AppE (ConE 'Field) (ConE 'Proxy)) (VarE v) | v <- varNames]
    let body = ListE fieldExprs
    return $ Clause [pat] (NormalB body) []
  RecC name fields -> genChildrenClause (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveLogicType: unsupported constructor form"

-- | Generate quote method (for pretty-printing)
-- Returns the constructor name and its children as fields.
genQuote :: [Con] -> Q Dec
genQuote cons = do
  clauses <- mapM genQuoteClause cons
  return $ FunD (mkName "quote") clauses

genQuoteClause :: Con -> Q Clause
genQuoteClause con = case con of
  NormalC name fields -> do
    let arity = length fields
        rName = mkName (nameBase name ++ "R")
    varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
    let pat = ConP rName [] (map VarP varNames)
    -- Body: (constructorName, [Field Proxy x1, Field Proxy x2, ...])
    let conNameStr = LitE (StringL (nameBase name))
    let fieldExprs = [AppE (AppE (ConE 'Field) (ConE 'Proxy)) (VarE v) | v <- varNames]
    let fieldList = ListE fieldExprs
    let body = TupE [Just conNameStr, Just fieldList]
    return $ Clause [pat] (NormalB body) []
  RecC name fields -> genQuoteClause (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveLogicType: unsupported constructor form"

getBuilderName :: [ConSpec] -> Name -> String
getBuilderName specMap name =
  case lookup name specMap of
    Just bname -> bname
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

-- | Generate moded constructors
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
genFieldOccursIn :: Name -> Name -> (Name, BangType) -> Q Exp
genFieldOccursIn nameType aName (varName, (_, fieldTy)) = do
  -- Check if field is a Bind of the same name type
  case fieldTy of
    AppT (AppT (ConT bindName) boundNameTy) _ | bindName == ''Bind -> do
      -- Check if the bound name type matches the name type we're checking
      case boundNameTy of
        ConT boundNameType | boundNameType == nameType -> do
          -- This is a Bind that binds our name type - generate shadowing check
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
-- Derive Substo (Capture-Avoiding Substitution)
--------------------------------------------------------------------------------

-- | Derive Substo instance for a type.
--
-- Takes the data type name and a list of (NameType, VarConstructor) pairs.
-- Each pair specifies which constructor holds a variable of that name type.
--
-- This is analogous to unbound-generics' @isvar@ escape hatch - you tell the
-- derivation which constructor represents a variable, and everything else
-- (recursion, binding, capture-avoidance) is handled automatically.
--
-- Usage:
--
-- @
-- -- For types: tau ::= Unit | alpha | tau1 -> tau2 | forall alpha. tau
-- data Ty = TUnit | TVar TyNom | TArr Ty Ty | TAll (Bind TyNom Ty)
--
-- deriveSubsto ''Ty [(''TyNom, 'TVar)]
-- -- Generates:
-- -- instance Substo TyNom Ty where
-- --   substo nameL bodyL replL resultL = do
-- --     body <- eval bodyL
-- --     case body of
-- --       TUnit -> resultL <=> Ground (project TUnit)
-- --       TVar v -> conde [nameL <=> ... >> resultL <=> replL, ...]
-- --       TArr t1 t2 -> freshLogic $ \\r1 -> freshLogic $ \\r2 -> ...
-- --       TAll (Bind alpha tyBody) -> conde [shadow, fresh+swap+recurse]
-- @
deriveSubsto :: Name -> [(Name, Name)] -> Q [Dec]
deriveSubsto typeName varSpecs = do
  info <- reify typeName
  case info of
    TyConI (DataD _ _ tvs _ cons _) -> do
      when (not (null tvs)) $
        fail "deriveSubsto: type must not have type variables"
      concat <$> mapM (genSubstoInstance typeName cons varSpecs) (map fst varSpecs)
    TyConI (NewtypeD _ _ tvs _ con _) -> do
      when (not (null tvs)) $
        fail "deriveSubsto: type must not have type variables"
      concat <$> mapM (genSubstoInstance typeName [con] varSpecs) (map fst varSpecs)
    _ -> fail "deriveSubsto: expected a data or newtype declaration"

-- | Generate a single Substo instance for a specific name type
genSubstoInstance :: Name -> [Con] -> [(Name, Name)] -> Name -> Q [Dec]
genSubstoInstance typeName cons varSpecs nameType = do
  -- Find the variable constructor for this name type
  let varCon = lookup nameType varSpecs

  -- Generate the substo function body
  nameL <- newName "nameL"
  bodyL <- newName "bodyL"
  replL <- newName "replL"
  resultL <- newName "resultL"
  bodyVar <- newName "body"

  -- Generate case alternatives for each constructor
  matches <- mapM (genSubstoMatch nameType varCon typeName nameL replL resultL) cons

  -- Build: do { body <- eval bodyL; case body of { ... } }
  let evalStmt = BindS (VarP bodyVar) (AppE (VarE 'eval) (VarE bodyL))
  let caseExpr = CaseE (VarE bodyVar) matches
  let doBody = DoE Nothing [evalStmt, NoBindS caseExpr]

  let clause = Clause [VarP nameL, VarP bodyL, VarP replL, VarP resultL] (NormalB doBody) []
  let substoDec = FunD (mkName "substo") [clause]

  let instType = AppT (AppT (ConT ''Substo) (ConT nameType)) (ConT typeName)
  return [InstanceD Nothing [] instType [substoDec]]

-- | Generate a match clause for a single constructor
genSubstoMatch :: Name -> Maybe Name -> Name -> Name -> Name -> Name -> Con -> Q Match
genSubstoMatch nameType mVarCon typeName nameL replL resultL con = case con of
  NormalC conName fields -> do
    let arity = length fields
        rName = mkName (nameBase conName ++ "R")

    if arity == 0
      then do
        -- Nullary: resultL <=> Ground (project Con)
        let body = InfixE (Just (VarE resultL)) (VarE '(<=>))
                     (Just (AppE (ConE 'Ground) (AppE (VarE 'project) (ConE conName))))
        return $ Match (ConP conName [] []) (NormalB body) []
      else do
        varNames <- mapM (\i -> newName ("x" ++ show i)) [1..arity]
        let pat = ConP conName [] (map VarP varNames)

        -- Check if this is the variable constructor
        case mVarCon of
          Just varConName | varConName == conName && arity == 1 -> do
            -- Variable case: conde [match/replace, hash/keep]
            let v = head varNames
            genVarCaseBody nameType nameL replL resultL conName rName v
          _ -> do
            -- Check for Bind fields and recursive fields
            genRecursiveCaseBody nameType typeName nameL replL resultL conName rName varNames fields

  RecC name fields -> genSubstoMatch nameType mVarCon typeName nameL replL resultL
                        (NormalC name [(b, t) | (_, b, t) <- fields])
  _ -> fail "deriveSubsto: unsupported constructor form"

-- | Generate the variable case: conde [match/replace, hash/keep]
genVarCaseBody :: Name -> Name -> Name -> Name -> Name -> Name -> Name -> Q Match
genVarCaseBody nameType nameL replL resultL conName rName v = do
  -- conde [ do { nameL <=> inject v; resultL <=> replL }
  --       , do { hash nameL (inject v); resultL <=> Ground (project (Con v)) } ]

  -- Build: Ground (project v)
  let injectV = AppE (ConE 'Ground) (AppE (VarE 'project) (VarE v))

  -- Branch 1: nameL <=> inject v >> resultL <=> replL
  let unifyName = InfixE (Just (VarE nameL)) (VarE '(<=>)) (Just injectV)
  let unifyResult1 = InfixE (Just (VarE resultL)) (VarE '(<=>)) (Just (VarE replL))
  let branch1 = DoE Nothing [NoBindS unifyName, NoBindS unifyResult1]

  -- Branch 2: hash nameL (inject v) >> resultL <=> Ground (project (Con v))
  let hashCall = foldl AppE (VarE 'hash) [VarE nameL, injectV]
  let keepResult = AppE (ConE 'Ground) (AppE (VarE 'project) (AppE (ConE conName) (VarE v)))
  let unifyResult2 = InfixE (Just (VarE resultL)) (VarE '(<=>)) (Just keepResult)
  let branch2 = DoE Nothing [NoBindS hashCall, NoBindS unifyResult2]

  let condeExpr = AppE (VarE 'conde) (ListE [branch1, branch2])

  return $ Match (ConP conName [] [VarP v]) (NormalB condeExpr) []

-- | Generate recursive case with freshLogic for each field
genRecursiveCaseBody :: Name -> Name -> Name -> Name -> Name -> Name -> Name -> [Name] -> [BangType] -> Q Match
genRecursiveCaseBody nameType typeName nameL replL resultL conName rName varNames fields = do
  -- Analyze each field
  fieldInfos <- forM (zip varNames fields) $ \(vn, (_, fieldTy)) ->
    analyzeFieldType nameType typeName fieldTy vn

  -- Check if any field is a Bind of the same name type
  let hasBindField = any (\case { BindField _ _ _ -> True; _ -> False }) fieldInfos

  if hasBindField
    then genBindCaseBody nameType nameL replL resultL conName rName varNames fields fieldInfos
    else genSimpleRecursiveBody nameType nameL replL resultL conName rName varNames fieldInfos

-- | Field classification for substitution
data FieldInfo
  = RecursiveField Name Name  -- field var, result var (needs substo)
  | BindField Name Name Name  -- field var, bound var name, body var name
  | NonRecursiveField Name    -- field var (no substo needed, different type)
  deriving Show

-- | Analyze a field type to determine how to handle it
analyzeFieldType :: Name -> Name -> Type -> Name -> Q FieldInfo
analyzeFieldType nameType typeName fieldTy varName = do
  case fieldTy of
    -- Bind nameType body - needs special handling
    AppT (AppT (ConT bindName) boundNameTy) bodyTy
      | bindName == ''Bind -> do
          case boundNameTy of
            ConT boundNameType | boundNameType == nameType -> do
              -- Same name type - needs shadow/fresh+swap
              bndVar <- newName "bnd"
              bodyVar <- newName "bdy"
              return $ BindField varName bndVar bodyVar
            _ -> do
              -- Different name type - just recurse on body if it's the target type
              if isTargetType typeName bodyTy
                then do
                  resVar <- newName "r"
                  return $ RecursiveField varName resVar
                else return $ NonRecursiveField varName

    -- Direct recursion on the same type
    ConT tyName | tyName == typeName -> do
      resVar <- newName "r"
      return $ RecursiveField varName resVar

    -- Other types - no substitution needed
    _ -> return $ NonRecursiveField varName

-- | Check if a type is the target type for substitution
isTargetType :: Name -> Type -> Bool
isTargetType typeName (ConT n) = n == typeName
isTargetType typeName (AppT t _) = isTargetType typeName t
isTargetType _ _ = False

-- | Generate simple recursive case (no Bind of same name type)
genSimpleRecursiveBody :: Name -> Name -> Name -> Name -> Name -> Name -> [Name] -> [FieldInfo] -> Q Match
genSimpleRecursiveBody nameType nameL replL resultL conName rName varNames fieldInfos = do
  -- Build nested freshLogic for recursive fields
  let recursiveFields = [(v, r) | RecursiveField v r <- fieldInfos]

  if null recursiveFields
    then do
      -- No recursive fields - just return unchanged
      let args = [VarE v | v <- varNames]
      let result = AppE (ConE 'Ground) (AppE (VarE 'project) (foldl AppE (ConE conName) args))
      let body = InfixE (Just (VarE resultL)) (VarE '(<=>)) (Just result)
      return $ Match (ConP conName [] (map VarP varNames)) (NormalB body) []
    else do
      -- Has recursive fields - generate freshLogic + substo calls
      let resultVars = [r | (_, r) <- recursiveFields]

      -- Build the innermost body: substo calls + result unification
      substoStmts <- forM recursiveFields $ \(v, r) -> do
        let grounded = AppE (ConE 'Ground) (AppE (VarE 'project) (VarE v))
        let call = foldl AppE (VarE 'substo) [VarE nameL, grounded, VarE replL, VarE r]
        return $ NoBindS call

      -- Build result: ConR with logic vars for recursive fields, Ground project for others
      let buildArg fi = case fi of
            RecursiveField _ r -> VarE r
            NonRecursiveField v -> AppE (ConE 'Ground) (AppE (VarE 'project) (VarE v))
            BindField v _ _ -> AppE (ConE 'Ground) (AppE (VarE 'project) (VarE v))
      let resultArgs = map buildArg fieldInfos
      let resultExpr = AppE (ConE 'Ground) (foldl AppE (ConE rName) resultArgs)
      let resultStmt = NoBindS $ InfixE (Just (VarE resultL)) (VarE '(<=>)) (Just resultExpr)

      let innerBody = DoE Nothing (substoStmts ++ [resultStmt])

      -- Wrap in freshLogic calls
      let wrapFreshLogic expr [] = expr
          wrapFreshLogic expr (r:rs) =
            AppE (VarE 'freshLogic) (LamE [VarP r] (wrapFreshLogic expr rs))

      let fullBody = wrapFreshLogic innerBody resultVars

      return $ Match (ConP conName [] (map VarP varNames)) (NormalB fullBody) []

-- | Generate Bind case with shadow/fresh+swap branches
genBindCaseBody :: Name -> Name -> Name -> Name -> Name -> Name -> [Name] -> [BangType] -> [FieldInfo] -> Q Match
genBindCaseBody nameType nameL replL resultL conName rName varNames fields fieldInfos = do
  -- Find the Bind field
  let bindInfo = head [(v, bnd, bdy) | BindField v bnd bdy <- fieldInfos]
  let (bindVar, _, _) = bindInfo

  -- Find the index of the bind field to extract bound name and body
  let bindIdx = head [i | (i, BindField _ _ _) <- zip [0..] fieldInfos]
  let (_, bindFieldTy) = fields !! bindIdx

  -- Extract body type from Bind nameType bodyTy
  let bodyTy = case bindFieldTy of
        AppT (AppT (ConT _) _) bt -> bt
        _ -> error "Expected Bind type"

  -- Generate pattern: Con x1 x2 ... (Bind alpha body) ...
  alphaName <- newName "alpha"
  bodyName <- newName "body"

  let patterns = [if i == bindIdx
                  then ConP 'Bind [] [VarP alphaName, VarP bodyName]
                  else VarP (varNames !! i)
                 | i <- [0..length varNames - 1]]

  -- Branch 1: Shadowed case
  let injectAlpha = AppE (ConE 'Ground) (AppE (VarE 'project) (VarE alphaName))
  let unifyName = InfixE (Just (VarE nameL)) (VarE '(<=>)) (Just injectAlpha)

  let origArgs = [if i == bindIdx
                  then AppE (AppE (ConE 'Bind) (VarE alphaName)) (VarE bodyName)
                  else VarE (varNames !! i)
                 | i <- [0..length varNames - 1]]
  let origResult = AppE (ConE 'Ground) (AppE (VarE 'project) (foldl AppE (ConE conName) origArgs))
  let unifyOrig = InfixE (Just (VarE resultL)) (VarE '(<=>)) (Just origResult)
  let shadowBranch = DoE Nothing [NoBindS unifyName, NoBindS unifyOrig]

  -- Branch 2: Substitute case with fresh+swap
  freshName <- newName "fresh"
  rBodyName <- newName "rBody"

  let hashAlpha = foldl AppE (VarE 'hash) [VarE nameL, injectAlpha]
  let injectFresh = AppE (ConE 'Ground) (AppE (VarE 'project) (VarE freshName))
  let hashFresh = foldl AppE (VarE 'hash) [injectFresh, VarE replL]

  let swapExpr = foldl AppE (VarE 'swap) [VarE alphaName, VarE freshName, VarE bodyName]
  swappedName <- newName "swappedBody"
  let swapLet = LetS [ValD (VarP swappedName) (NormalB swapExpr) []]

  let grounded = AppE (ConE 'Ground) (AppE (VarE 'project) (VarE swappedName))
  let substoCall = foldl AppE (VarE 'substo) [VarE nameL, grounded, VarE replL, VarE rBodyName]

  let bindExpr = foldl AppE (VarE 'bind) [VarE freshName, VarE rBodyName]
  let resultArgs = [if i == bindIdx
                    then bindExpr
                    else AppE (ConE 'Ground) (AppE (VarE 'project) (VarE (varNames !! i)))
                   | i <- [0..length varNames - 1]]
  let resultExpr = AppE (ConE 'Ground) (foldl AppE (ConE rName) resultArgs)
  let unifyResult = InfixE (Just (VarE resultL)) (VarE '(<=>)) (Just resultExpr)

  let innerStmts = [NoBindS hashAlpha, NoBindS hashFresh, swapLet, NoBindS substoCall, NoBindS unifyResult]
  let innerBody = DoE Nothing innerStmts

  let withRBody = AppE (VarE 'freshLogic) (LamE [VarP rBodyName] innerBody)
  let withFresh = AppE (VarE 'freshOne) (LamE [VarP freshName] withRBody)
  let substBranch = withFresh

  let condeExpr = AppE (VarE 'conde) (ListE [shadowBranch, substBranch])

  return $ Match (ConP conName [] patterns) (NormalB condeExpr) []
