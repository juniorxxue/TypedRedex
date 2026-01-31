{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module STLC.Syntax
  ( Ty(..)
  , Tm(..)
  , Env(..)
  , tint
  , tbool
  , tarr
  , lit
  , true
  , false
  , var
  , lam
  , app
  , plus
  , ifte
  , eempty
  , ebind
  ) where

{-

type A, B =  int | bool | A -> B

expression e := x
              | \x:A. e
              | e e
              | n
              | e1 + e2
              | true
              | false
              | if e1 then e2 else e3

values v := n | true | false | \x:A. e

small-step semantics:

    (β)    (\x:A. e) v  -->  e[v/x]
    (δ+)   n1 + n2  -->  n3   where n3 = n1 + n2
    (ifT)  if true then e2 else e3  -->  e2
    (ifF)  if false then e2 else e3  -->  e3

congruence rules:

    (app1)  e1 --> e1'  implies  e1 e2  -->  e1' e2
    (app2)  e2 --> e2'  implies  v1 e2  -->  v1 e2'   where v1 is a value
    (ifC)   e1 --> e1'  implies  if e1 then e2 else e3  -->  if e1' then e2 else e3

typing rules:

    (T-Var)      Γ(x) = A
                 ----------------
                 Γ ⊢ x : A

    (T-Abs)      Γ, x:A ⊢ e : B
                 ----------------------
                 Γ ⊢ \x:A. e : A -> B

    (T-App)      Γ ⊢ e1 : A -> B    Γ ⊢ e2 : A
                 --------------------------------
                 Γ ⊢ e1 e2 : B

    (T-Lit)      ----------------
                 Γ ⊢ n : int

    (T-Add)      Γ ⊢ e1 : int    Γ ⊢ e2 : int
                 -------------------------------
                 Γ ⊢ e1 + e2 : int

    (T-True)     ----------------
                 Γ ⊢ true : bool

    (T-False)    ----------------
                 Γ ⊢ false : bool

    (T-If)       Γ ⊢ e1 : bool    Γ ⊢ e2 : A    Γ ⊢ e3 : A
                 -------------------------------------------
                 Γ ⊢ if e1 then e2 else e3 : A

progress:

    If ⊢ e : A, then either e is a value or there exists e' such that e --> e'.

preservation:

    If ⊢ e : A and e --> e', then ⊢ e' : A.

-}

import TypedRedex.Core.Term hiding (var)
import TypedRedex.Nominal (NominalAtom, Permute(..), Hash(..))
import TypedRedex.Nominal.Bind (Bind(..), bind, unbind)
import TypedRedex.Nominal.Prelude (Nom)
import TypedRedex.Pretty (Pretty(..), PrettyM, Doc(..), (<+>), parens, prettyLogic, cycleNames)
import Support.Nat (Nat)

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

data Ty
  = TyInt
  | TyBool
  | TyArr Ty Ty
  deriving (Eq, Show)

data Tm
  = TmVar Nom
  | Lit Nat
  | Lam Ty (Bind Nom Tm)
  | App Tm Tm
  | Plus Tm Tm
  | BTrue
  | BFalse
  | If Tm Tm Tm
  deriving (Eq, Show)

-- | Typing environment Γ.
data Env
  = EEmpty
  | EBind Nom Ty Env
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Repr instances
--------------------------------------------------------------------------------

instance Repr Ty where
  data Reified Ty
    = RTInt
    | RTBool
    | RTArr (Logic Ty) (Logic Ty)

  project TyInt = RTInt
  project TyBool = RTBool
  project (TyArr a b) = RTArr (Ground (project a)) (Ground (project b))

  reify RTInt = Just TyInt
  reify RTBool = Just TyBool
  reify (RTArr (Ground a) (Ground b)) = TyArr <$> reify a <*> reify b
  reify _ = Nothing

  quote RTInt = ("int", [])
  quote RTBool = ("bool", [])
  quote (RTArr a b) = ("Arr", [Field a, Field b])

  mapReified _ RTInt = RTInt
  mapReified _ RTBool = RTBool
  mapReified f (RTArr a b) = RTArr (f a) (f b)

instance Repr Tm where
  data Reified Tm
    = RVar (Logic Nom)
    | RLit (Logic Nat)
    | RLam (Logic Ty) (Logic (Bind Nom Tm))
    | RApp (Logic Tm) (Logic Tm)
    | RPlus (Logic Tm) (Logic Tm)
    | RTrue
    | RFalse
    | RIf (Logic Tm) (Logic Tm) (Logic Tm)

  project (TmVar x) = RVar (Ground (project x))
  project (Lit n) = RLit (Ground (project n))
  project (Lam ty bnd) = RLam (Ground (project ty)) (Ground (project bnd))
  project (App t1 t2) = RApp (Ground (project t1)) (Ground (project t2))
  project (Plus t1 t2) = RPlus (Ground (project t1)) (Ground (project t2))
  project BTrue = RTrue
  project BFalse = RFalse
  project (If c t e) = RIf (Ground (project c)) (Ground (project t)) (Ground (project e))

  reify (RVar (Ground x)) = TmVar <$> reify x
  reify (RLit (Ground n)) = Lit <$> reify n
  reify (RLam (Ground ty) (Ground bnd)) = Lam <$> reify ty <*> reify bnd
  reify (RApp (Ground t1) (Ground t2)) = App <$> reify t1 <*> reify t2
  reify (RPlus (Ground t1) (Ground t2)) = Plus <$> reify t1 <*> reify t2
  reify RTrue = Just BTrue
  reify RFalse = Just BFalse
  reify (RIf (Ground c) (Ground t) (Ground e)) = If <$> reify c <*> reify t <*> reify e
  reify _ = Nothing

  quote (RVar x) = ("Var", [Field x])
  quote (RLit n) = ("Lit", [Field n])
  quote (RLam ty bnd) = ("Lam", [Field ty, Field bnd])
  quote (RApp t1 t2) = ("App", [Field t1, Field t2])
  quote (RPlus t1 t2) = ("Plus", [Field t1, Field t2])
  quote RTrue = ("true", [])
  quote RFalse = ("false", [])
  quote (RIf c t e) = ("If", [Field c, Field t, Field e])

  mapReified f r =
    case r of
      RVar x -> RVar (f x)
      RLit n -> RLit (f n)
      RLam ty bnd -> RLam (f ty) (f bnd)
      RApp t1 t2 -> RApp (f t1) (f t2)
      RPlus t1 t2 -> RPlus (f t1) (f t2)
      RTrue -> RTrue
      RFalse -> RFalse
      RIf c t e -> RIf (f c) (f t) (f e)

instance Repr Env where
  data Reified Env
    = REmpty
    | RExt (Logic Nom) (Logic Ty) (Logic Env)

  project EEmpty = REmpty
  project (EBind x ty env) = RExt (Ground (project x)) (Ground (project ty)) (Ground (project env))

  reify REmpty = Just EEmpty
  reify (RExt (Ground x) (Ground ty) (Ground env)) = EBind <$> reify x <*> reify ty <*> reify env
  reify _ = Nothing

  quote REmpty = (".", [])
  quote (RExt x ty env) = ("Bind", [Field x, Field ty, Field env])

  mapReified _ REmpty = REmpty
  mapReified f (RExt x ty env) = RExt (f x) (f ty) (f env)

--------------------------------------------------------------------------------
-- Pretty instances
--------------------------------------------------------------------------------

instance Pretty Ty where
  varNames = cycleNames ["A", "B", "C", "D"]
  prettyReified RTInt = pure "int"
  prettyReified RTBool = pure "bool"
  prettyReified (RTArr a b) = do
    da <- prettyTyDom a
    db <- prettyLogic b
    pure (da <+> Doc " -> " <+> db)
    where
      -- Parenthesize the domain when it is itself an arrow.
      prettyTyDom :: Logic Ty -> PrettyM Doc
      prettyTyDom t@(Ground (RTArr _ _)) = parens <$> prettyLogic t
      prettyTyDom t = prettyLogic t

instance Pretty Tm where
  varNames = cycleNames ["e"]
  prettyReified (RVar x) = prettyLogic x
  prettyReified (RLit n) = prettyLogic n
  prettyReified (RLam ty bnd) = do
    (dx, db) <- prettyBind bnd
    dty <- prettyLogic ty
    pure (Doc "\\" <+> dx <+> Doc " : " <+> dty <+> Doc ". " <+> db)
  prettyReified (RApp t1 t2) = do
    d1 <- prettyLogic t1
    d2 <- prettyLogic t2
    pure (parens (d1 <+> Doc " " <+> d2))
  prettyReified (RPlus t1 t2) = do
    d1 <- prettyLogic t1
    d2 <- prettyLogic t2
    pure (parens (d1 <+> Doc " + " <+> d2))
  prettyReified RTrue = pure "true"
  prettyReified RFalse = pure "false"
  prettyReified (RIf c t e) = do
    dc <- prettyLogic c
    dt <- prettyLogic t
    de <- prettyLogic e
    pure (Doc "if " <+> dc <+> Doc " then " <+> dt <+> Doc " else " <+> de)

instance Pretty Env where
  varNames = cycleNames ["Γ"]
  prettyReified REmpty = pure "."
  prettyReified (RExt x ty env) = do
    dx <- prettyLogic x
    dty <- prettyLogic ty
    denv <- prettyLogic env
    pure (denv <+> Doc ", " <+> dx <+> Doc ":" <+> dty)

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

--------------------------------------------------------------------------------
-- Permute/Hash instances
--------------------------------------------------------------------------------

instance Permute Nom Ty where
  swap _ _ ty = ty

instance Permute Nom Tm where
  swap a b tm =
    case tm of
      TmVar x -> TmVar (swap a b x)
      Lit n -> Lit n
      Lam ty bnd -> Lam ty (swap a b bnd)
      App t1 t2 -> App (swap a b t1) (swap a b t2)
      Plus t1 t2 -> Plus (swap a b t1) (swap a b t2)
      BTrue -> BTrue
      BFalse -> BFalse
      If c t e -> If (swap a b c) (swap a b t) (swap a b e)

instance Permute Nom Env where
  swap a b env =
    case env of
      EEmpty -> EEmpty
      EBind x ty rest -> EBind (swap a b x) ty (swap a b rest)

instance Hash Nom Ty where
  occursIn _ _ = False

instance Hash Nom Tm where
  occursIn a tm =
    case tm of
      TmVar b -> a == b
      Lit _ -> False
      Lam _ (Bind b body) ->
        if a == b
          then False
          else occursIn a body
      App t1 t2 -> occursIn a t1 || occursIn a t2
      Plus t1 t2 -> occursIn a t1 || occursIn a t2
      BTrue -> False
      BFalse -> False
      If c t e -> occursIn a c || occursIn a t || occursIn a e

--------------------------------------------------------------------------------
-- Smart constructors (logic terms)
--------------------------------------------------------------------------------

tint :: Term Ty
tint = ground TyInt

tbool :: Term Ty
tbool = ground TyBool

tarr :: Term Ty -> Term Ty -> Term Ty
tarr = lift2 (\a b -> Ground (RTArr a b))

lit :: Term Nat -> Term Tm
lit = lift1 (\n -> Ground (RLit n))

true :: Term Tm
true = ground BTrue

false :: Term Tm
false = ground BFalse

var :: Term Nom -> Term Tm
var = lift1 (\x -> Ground (RVar x))

lam :: Term Ty -> Term Nom -> Term Tm -> Term Tm
lam ty x body =
  lift2 (\ty' bnd -> Ground (RLam ty' bnd)) ty (bind x body)

app :: Term Tm -> Term Tm -> Term Tm
app = lift2 (\t1 t2 -> Ground (RApp t1 t2))

plus :: Term Tm -> Term Tm -> Term Tm
plus = lift2 (\t1 t2 -> Ground (RPlus t1 t2))

ifte :: Term Tm -> Term Tm -> Term Tm -> Term Tm
ifte = lift3 (\c t e -> Ground (RIf c t e))

eempty :: Term Env
eempty = ground EEmpty

ebind :: Term Nom -> Term Ty -> Term Env -> Term Env
ebind = lift3 (\x ty env -> Ground (RExt x ty env))

