{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Signal.Syntax
  ( Ty(..)
  , Tm(..)
  , Polar(..)
  , Env(..)
  , Context(..)
  , tint
  , tbool
  , tvar
  , tarr
  , tforall
  , lit
  , true
  , false
  , var
  , plus
  , lam
  , app
  , ann
  , tlam
  , tapp
  , pos
  , neg
  , eempty
  , etrm
  , euvar
  , eevar
  , esvar
  , cempty
  , ctype
  , ctm
  ) where

import TypedRedex.Core.Term hiding (var)
import TypedRedex.Nominal (NominalAtom, Permute(..), Hash(..))
import TypedRedex.Nominal.Bind (Bind(..), bind, unbind)
import TypedRedex.Nominal.Prelude (Nom, TyNom)
import TypedRedex.Pretty (Pretty(..), PrettyM, Doc(..), (<+>), parens, prettyLogic, cycleNames)
import Support.Nat (Nat)

--------------------------------------------------------------------------------
-- Syntax (same as Poly)
--------------------------------------------------------------------------------

data Ty
  = TyInt
  | TyBool
  | TyVar TyNom
  | TyArr Ty Ty
  | TyForall (Bind TyNom Ty)
  deriving (Eq, Show)

data Tm
  = Literal Nat
  | BTrue
  | BFalse
  | TmVar Nom
  | Plus Tm Tm
  | Abs (Bind Nom Tm)
  | App Tm Tm
  | Ann Tm Ty
  | TAbs (Bind TyNom Tm)
  | TApp Tm Ty
  deriving (Eq, Show)

data Polar
  = Pos
  | Neg
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Environment (closer to LCTI)
--------------------------------------------------------------------------------

data Env
  = EEmpty
  | ETrm Nom Ty Env
  | EUvar TyNom Env       -- universal type variable
  | EEvar TyNom Env       -- existential type variable (unsolved)
  | ESvar TyNom Ty Env    -- solved existential type variable
  deriving (Eq, Show)

data Context
  = CEmpty
  | CType Ty
  | CTm Tm Context
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Repr instances
--------------------------------------------------------------------------------

instance Repr Ty where
  data Reified Ty
    = RTInt
    | RTBool
    | RTVar (Logic TyNom)
    | RTArr (Logic Ty) (Logic Ty)
    | RTForall (Logic (Bind TyNom Ty))

  project TyInt = RTInt
  project TyBool = RTBool
  project (TyVar a) = RTVar (Ground (project a))
  project (TyArr a b) = RTArr (Ground (project a)) (Ground (project b))
  project (TyForall bnd) = RTForall (Ground (project bnd))

  reify RTInt = Just TyInt
  reify RTBool = Just TyBool
  reify (RTVar (Ground a)) = TyVar <$> reify a
  reify (RTArr (Ground a) (Ground b)) = TyArr <$> reify a <*> reify b
  reify (RTForall (Ground bnd)) = TyForall <$> reify bnd
  reify _ = Nothing

  quote RTInt = ("Int", [])
  quote RTBool = ("Bool", [])
  quote (RTVar a) = ("Var", [Field a])
  quote (RTArr a b) = ("Arr", [Field a, Field b])
  quote (RTForall bnd) = ("Forall", [Field bnd])

  mapReified _ RTInt = RTInt
  mapReified _ RTBool = RTBool
  mapReified f (RTVar a) = RTVar (f a)
  mapReified f (RTArr a b) = RTArr (f a) (f b)
  mapReified f (RTForall bnd) = RTForall (f bnd)

instance Repr Tm where
  data Reified Tm
    = RLit (Logic Nat)
    | RTrue
    | RFalse
    | RVar (Logic Nom)
    | RPlus (Logic Tm) (Logic Tm)
    | RAbs (Logic (Bind Nom Tm))
    | RApp (Logic Tm) (Logic Tm)
    | RAnn (Logic Tm) (Logic Ty)
    | RTAbs (Logic (Bind TyNom Tm))
    | RTApp (Logic Tm) (Logic Ty)

  project (Literal n) = RLit (Ground (project n))
  project BTrue = RTrue
  project BFalse = RFalse
  project (TmVar x) = RVar (Ground (project x))
  project (Plus t1 t2) = RPlus (Ground (project t1)) (Ground (project t2))
  project (Abs bnd) = RAbs (Ground (project bnd))
  project (App t1 t2) = RApp (Ground (project t1)) (Ground (project t2))
  project (Ann t ty) = RAnn (Ground (project t)) (Ground (project ty))
  project (TAbs bnd) = RTAbs (Ground (project bnd))
  project (TApp t ty) = RTApp (Ground (project t)) (Ground (project ty))

  reify (RLit (Ground n)) = Literal <$> reify n
  reify RTrue = Just BTrue
  reify RFalse = Just BFalse
  reify (RVar (Ground x)) = TmVar <$> reify x
  reify (RPlus (Ground t1) (Ground t2)) = Plus <$> reify t1 <*> reify t2
  reify (RAbs (Ground bnd)) = Abs <$> reify bnd
  reify (RApp (Ground t1) (Ground t2)) = App <$> reify t1 <*> reify t2
  reify (RAnn (Ground t) (Ground ty)) = Ann <$> reify t <*> reify ty
  reify (RTAbs (Ground bnd)) = TAbs <$> reify bnd
  reify (RTApp (Ground t) (Ground ty)) = TApp <$> reify t <*> reify ty
  reify _ = Nothing

  quote (RLit n) = ("Lit", [Field n])
  quote RTrue = ("True", [])
  quote RFalse = ("False", [])
  quote (RVar x) = ("Var", [Field x])
  quote (RPlus t1 t2) = ("Plus", [Field t1, Field t2])
  quote (RAbs bnd) = ("Lam", [Field bnd])
  quote (RApp t1 t2) = ("App", [Field t1, Field t2])
  quote (RAnn t ty) = ("Ann", [Field t, Field ty])
  quote (RTAbs bnd) = ("TLam", [Field bnd])
  quote (RTApp t ty) = ("TApp", [Field t, Field ty])

  mapReified f (RLit n) = RLit (f n)
  mapReified _ RTrue = RTrue
  mapReified _ RFalse = RFalse
  mapReified f (RVar x) = RVar (f x)
  mapReified f (RPlus t1 t2) = RPlus (f t1) (f t2)
  mapReified f (RAbs bnd) = RAbs (f bnd)
  mapReified f (RApp t1 t2) = RApp (f t1) (f t2)
  mapReified f (RAnn t ty) = RAnn (f t) (f ty)
  mapReified f (RTAbs bnd) = RTAbs (f bnd)
  mapReified f (RTApp t ty) = RTApp (f t) (f ty)

instance Repr Polar where
  data Reified Polar = RPos | RNeg

  project Pos = RPos
  project Neg = RNeg

  reify RPos = Just Pos
  reify RNeg = Just Neg

  quote RPos = ("Pos", [])
  quote RNeg = ("Neg", [])

  mapReified _ RPos = RPos
  mapReified _ RNeg = RNeg

instance Repr Env where
  data Reified Env
    = REmpty
    | RTrm (Logic Nom) (Logic Ty) (Logic Env)
    | RUvar (Logic TyNom) (Logic Env)
    | REvar (Logic TyNom) (Logic Env)
    | RSvar (Logic TyNom) (Logic Ty) (Logic Env)

  project EEmpty = REmpty
  project (ETrm x ty env) = RTrm (Ground (project x)) (Ground (project ty)) (Ground (project env))
  project (EUvar a env) = RUvar (Ground (project a)) (Ground (project env))
  project (EEvar a env) = REvar (Ground (project a)) (Ground (project env))
  project (ESvar a ty env) = RSvar (Ground (project a)) (Ground (project ty)) (Ground (project env))

  reify REmpty = Just EEmpty
  reify (RTrm (Ground x) (Ground ty) (Ground env)) = ETrm <$> reify x <*> reify ty <*> reify env
  reify (RUvar (Ground a) (Ground env)) = EUvar <$> reify a <*> reify env
  reify (REvar (Ground a) (Ground env)) = EEvar <$> reify a <*> reify env
  reify (RSvar (Ground a) (Ground ty) (Ground env)) = ESvar <$> reify a <*> reify ty <*> reify env
  reify _ = Nothing

  quote REmpty = ("Empty", [])
  quote (RTrm x ty env) = ("ETrm", [Field x, Field ty, Field env])
  quote (RUvar a env) = ("EUvar", [Field a, Field env])
  quote (REvar a env) = ("EEvar", [Field a, Field env])
  quote (RSvar a ty env) = ("ESvar", [Field a, Field ty, Field env])

  mapReified _ REmpty = REmpty
  mapReified f (RTrm x ty env) = RTrm (f x) (f ty) (f env)
  mapReified f (RUvar a env) = RUvar (f a) (f env)
  mapReified f (REvar a env) = REvar (f a) (f env)
  mapReified f (RSvar a ty env) = RSvar (f a) (f ty) (f env)

instance Repr Context where
  data Reified Context
    = RCEmpty
    | RCType (Logic Ty)
    | RCTm (Logic Tm) (Logic Context)

  project CEmpty = RCEmpty
  project (CType ty) = RCType (Ground (project ty))
  project (CTm tm ctx) = RCTm (Ground (project tm)) (Ground (project ctx))

  reify RCEmpty = Just CEmpty
  reify (RCType (Ground ty)) = CType <$> reify ty
  reify (RCTm (Ground tm) (Ground ctx)) = CTm <$> reify tm <*> reify ctx
  reify _ = Nothing

  quote RCEmpty = ("CEmpty", [])
  quote (RCType ty) = ("CType", [Field ty])
  quote (RCTm tm ctx) = ("CTm", [Field tm, Field ctx])

  mapReified _ RCEmpty = RCEmpty
  mapReified f (RCType ty) = RCType (f ty)
  mapReified f (RCTm tm ctx) = RCTm (f tm) (f ctx)

--------------------------------------------------------------------------------
-- Pretty instances
--------------------------------------------------------------------------------

instance Pretty Ty where
  varNames = cycleNames ["A", "B", "C", "D"]
  prettyReified RTInt = pure "int"
  prettyReified RTBool = pure "bool"
  prettyReified (RTVar a) = prettyLogic a
  prettyReified (RTArr a b) = do
    da <- prettyLogic a
    db <- prettyLogic b
    pure (parens (da <+> " -> " <+> db))
  prettyReified (RTForall bnd) = prettyForall bnd

instance Pretty Tm where
  varNames = cycleNames ["e"]
  prettyReified (RLit n) = prettyLogic n
  prettyReified RTrue = pure "true"
  prettyReified RFalse = pure "false"
  prettyReified (RVar x) = prettyLogic x
  prettyReified (RPlus t1 t2) = do
    d1 <- prettyLogic t1
    d2 <- prettyLogic t2
    pure (parens (d1 <+> " + " <+> d2))
  prettyReified (RAbs bnd) = do
    (dn, db) <- prettyBind bnd
    pure (Doc "\\" <+> dn <+> Doc ". " <+> db)
  prettyReified (RApp t1 t2) = do
    d1 <- prettyLogic t1
    d2 <- prettyLogic t2
    pure (parens (d1 <+> " " <+> d2))
  prettyReified (RAnn t ty) = do
    dt <- prettyLogic t
    dty <- prettyLogic ty
    pure (parens (dt <+> " : " <+> dty))
  prettyReified (RTAbs bnd) = do
    (dn, db) <- prettyBind bnd
    pure (Doc "/\\" <+> dn <+> Doc ". " <+> db)
  prettyReified (RTApp t ty) = do
    dt <- prettyLogic t
    dty <- prettyLogic ty
    pure (dt <+> Doc " [" <+> dty <+> Doc "]")

instance Pretty Polar where
  varNames = cycleNames ["p"]
  prettyReified RPos = pure "+"
  prettyReified RNeg = pure "-"

instance Pretty Env where
  varNames = cycleNames ["G"]
  prettyReified REmpty = pure "."
  prettyReified (RTrm x ty env) = do
    dx <- prettyLogic x
    dty <- prettyLogic ty
    denv <- prettyLogic env
    pure (denv <+> ", " <+> dx <+> ":" <+> dty)
  prettyReified (RUvar a env) = do
    da <- prettyLogic a
    denv <- prettyLogic env
    pure (denv <+> ", " <+> da)
  prettyReified (REvar a env) = do
    da <- prettyLogic a
    denv <- prettyLogic env
    pure (denv <+> ", ^" <+> da)
  prettyReified (RSvar a ty env) = do
    da <- prettyLogic a
    dty <- prettyLogic ty
    denv <- prettyLogic env
    pure (denv <+> ", " <+> da <+> " = " <+> dty)

instance Pretty Context where
  varNames = cycleNames ["S"]
  prettyReified RCEmpty = pure "[]"
  prettyReified (RCType ty) = prettyLogic ty
  prettyReified (RCTm tm ctx) = do
    dtm <- prettyLogic tm
    dctx <- prettyLogic ctx
    pure (dtm <+> " ~> " <+> dctx)

prettyBind
  :: forall name body.
     (NominalAtom name, Permute name body, Hash name body, Pretty name, Pretty body)
  => Logic (Bind name body)
  -> PrettyM (Doc, Doc)
prettyBind bnd =
  case unbind bnd of
    Just (n, body) -> do
      dn <- prettyLogic n
      db <- prettyLogic body
      pure (dn, db)
    Nothing -> do
      d <- prettyLogic bnd
      pure (d, d)

prettyForall
  :: Logic (Bind TyNom Ty)
  -> PrettyM Doc
prettyForall bnd = do
  (dn, db) <- prettyBind bnd
  pure (Doc "forall " <+> dn <+> Doc ". " <+> db)

--------------------------------------------------------------------------------
-- Permute/Hash instances
--------------------------------------------------------------------------------

instance Permute TyNom Ty where
  swap a b ty =
    case ty of
      TyInt -> TyInt
      TyBool -> TyBool
      TyVar x -> TyVar (swap a b x)
      TyArr t1 t2 -> TyArr (swap a b t1) (swap a b t2)
      TyForall bnd -> TyForall (swap a b bnd)

instance Permute TyNom Tm where
  swap a b tm =
    case tm of
      Literal n -> Literal n
      BTrue -> BTrue
      BFalse -> BFalse
      TmVar x -> TmVar x
      Plus t1 t2 -> Plus (swap a b t1) (swap a b t2)
      Abs bnd -> Abs (swap a b bnd)
      App t1 t2 -> App (swap a b t1) (swap a b t2)
      Ann t ty -> Ann (swap a b t) (swap a b ty)
      TAbs bnd -> TAbs (swap a b bnd)
      TApp t ty -> TApp (swap a b t) (swap a b ty)

instance Permute Nom Tm where
  swap a b tm =
    case tm of
      Literal n -> Literal n
      BTrue -> BTrue
      BFalse -> BFalse
      TmVar x -> TmVar (swap a b x)
      Plus t1 t2 -> Plus (swap a b t1) (swap a b t2)
      Abs bnd -> Abs (swap a b bnd)
      App t1 t2 -> App (swap a b t1) (swap a b t2)
      Ann t ty -> Ann (swap a b t) ty
      TAbs bnd -> TAbs bnd
      TApp t ty -> TApp (swap a b t) ty

instance Permute TyNom Env where
  swap a b env =
    case env of
      EEmpty -> EEmpty
      ETrm x ty rest -> ETrm x (swap a b ty) (swap a b rest)
      EUvar n rest -> EUvar (swap a b n) (swap a b rest)
      EEvar n rest -> EEvar (swap a b n) (swap a b rest)
      ESvar n ty rest -> ESvar (swap a b n) (swap a b ty) (swap a b rest)

instance Permute Nom Env where
  swap a b env =
    case env of
      EEmpty -> EEmpty
      ETrm x ty rest -> ETrm (swap a b x) ty (swap a b rest)
      EUvar n rest -> EUvar n (swap a b rest)
      EEvar n rest -> EEvar n (swap a b rest)
      ESvar n ty rest -> ESvar n ty (swap a b rest)

instance Permute TyNom Context where
  swap a b ctx =
    case ctx of
      CEmpty -> CEmpty
      CType ty -> CType (swap a b ty)
      CTm tm rest -> CTm (swap a b tm) (swap a b rest)

instance Permute Nom Context where
  swap a b ctx =
    case ctx of
      CEmpty -> CEmpty
      CType ty -> CType ty
      CTm tm rest -> CTm (swap a b tm) (swap a b rest)

instance Hash TyNom Ty where
  occursIn a ty =
    case ty of
      TyInt -> False
      TyBool -> False
      TyVar b -> a == b
      TyArr t1 t2 -> occursIn a t1 || occursIn a t2
      TyForall (Bind b body) ->
        if a == b
          then False
          else occursIn a body

instance Hash TyNom Tm where
  occursIn a tm =
    case tm of
      Literal _ -> False
      BTrue -> False
      BFalse -> False
      TmVar _ -> False
      Plus t1 t2 -> occursIn a t1 || occursIn a t2
      Abs (Bind _ body) -> occursIn a body
      App t1 t2 -> occursIn a t1 || occursIn a t2
      Ann t ty -> occursIn a t || occursIn a ty
      TAbs (Bind b body) ->
        if a == b
          then False
          else occursIn a body
      TApp t ty -> occursIn a t || occursIn a ty

instance Hash Nom Tm where
  occursIn a tm =
    case tm of
      Literal _ -> False
      BTrue -> False
      BFalse -> False
      TmVar b -> a == b
      Plus t1 t2 -> occursIn a t1 || occursIn a t2
      Abs (Bind b body) ->
        if a == b
          then False
          else occursIn a body
      App t1 t2 -> occursIn a t1 || occursIn a t2
      Ann t _ -> occursIn a t
      TAbs (Bind _ body) -> occursIn a body
      TApp t _ -> occursIn a t

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

tint :: Term Ty
tint = ground TyInt

tbool :: Term Ty
tbool = ground TyBool

tvar :: Term TyNom -> Term Ty
tvar = lift1 (\a -> Ground (RTVar a))

tarr :: Term Ty -> Term Ty -> Term Ty
tarr = lift2 (\a b -> Ground (RTArr a b))

tforall :: Term TyNom -> Term Ty -> Term Ty
tforall a body =
  lift1 (\bnd -> Ground (RTForall bnd)) (bind a body)

lit :: Term Nat -> Term Tm
lit = lift1 (\n -> Ground (RLit n))

true :: Term Tm
true = ground BTrue

false :: Term Tm
false = ground BFalse

var :: Term Nom -> Term Tm
var = lift1 (\x -> Ground (RVar x))

plus :: Term Tm -> Term Tm -> Term Tm
plus = lift2 (\t1 t2 -> Ground (RPlus t1 t2))

lam :: Term Nom -> Term Tm -> Term Tm
lam x body =
  lift1 (\bnd -> Ground (RAbs bnd)) (bind x body)

app :: Term Tm -> Term Tm -> Term Tm
app = lift2 (\t1 t2 -> Ground (RApp t1 t2))

ann :: Term Tm -> Term Ty -> Term Tm
ann = lift2 (\t ty -> Ground (RAnn t ty))

tlam :: Term TyNom -> Term Tm -> Term Tm
tlam a body =
  lift1 (\bnd -> Ground (RTAbs bnd)) (bind a body)

tapp :: Term Tm -> Term Ty -> Term Tm
tapp = lift2 (\t ty -> Ground (RTApp t ty))

pos :: Term Polar
pos = ground Pos

neg :: Term Polar
neg = ground Neg

eempty :: Term Env
eempty = ground EEmpty

etrm :: Term Nom -> Term Ty -> Term Env -> Term Env
etrm = lift3 (\x ty env -> Ground (RTrm x ty env))

euvar :: Term TyNom -> Term Env -> Term Env
euvar = lift2 (\a env -> Ground (RUvar a env))

eevar :: Term TyNom -> Term Env -> Term Env
eevar = lift2 (\a env -> Ground (REvar a env))

esvar :: Term TyNom -> Term Ty -> Term Env -> Term Env
esvar = lift3 (\a ty env -> Ground (RSvar a ty env))

cempty :: Term Context
cempty = ground CEmpty

ctype :: Term Ty -> Term Context
ctype = lift1 (\ty -> Ground (RCType ty))

ctm :: Term Tm -> Term Context -> Term Context
ctm = lift2 (\tm ctx -> Ground (RCTm tm ctx))
