{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Complete example of the Labels-based Display DSL.
--
-- Shows how users write display rules using #labels that match
-- their smart constructor names - no naming conflicts!
module TypedRedex.Free.Display.LabelsExample where

import TypedRedex.Free.Display.Labels

--------------------------------------------------------------------------------
-- User's Original Types
--------------------------------------------------------------------------------

data Nat = Z | S Nat
  deriving (Eq, Show)

data Ty = TUnit | TArr Ty Ty
  deriving (Eq, Show)

data Tm
  = Var Nat
  | Unit
  | Lam Tm
  | App Tm Tm
  | Ann Tm Ty
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Display Rules (What Users Write!)
--
-- Labels match the smart constructor names: #var, #lam, #app, etc.
-- Using <+> avoids type annotations - clean and simple!
--------------------------------------------------------------------------------

natDisplay :: Display Nat
natDisplay = display
  [ #z   ~= "0"
  , #suc ~> \n -> "S " <+> n
  ]

tyDisplay :: Display Ty
tyDisplay = display
  [ #tunit ~= "Unit"
  , #tarr  ~> \(a, b) -> a <+> " → " <+> b
  ]

tmDisplay :: Display Tm
tmDisplay = display
  [ #var  ~> \n -> "var " <+> n
  , #unit ~= "()"
  , #lam  ~> \b -> "λ. " <+> b
  , #app  ~> \(f, x) -> f <+> " " <+> x
  , #ann  ~> \(e, t) -> e <+> " : " <+> t
  ]

--------------------------------------------------------------------------------
-- Logic Types (Simplified)
--------------------------------------------------------------------------------

data Logic a var
  = Free var
  | Ground (Reified a var)

data family Reified a var

data instance Reified Nat var = ZR | SR (Logic Nat var)
data instance Reified Ty var = TUnitR | TArrR (Logic Ty var) (Logic Ty var)
data instance Reified Tm var
  = VarR (Logic Nat var)
  | UnitR
  | LamR (Logic Tm var)
  | AppR (Logic Tm var) (Logic Tm var)
  | AnnR (Logic Tm var) (Logic Ty var)

--------------------------------------------------------------------------------
-- Bridge: FromDisplay Class
--
-- Connects Reified to Display using constructor name lookup.
--------------------------------------------------------------------------------

class FromDisplay a where
  -- | Get the display table for this type
  displayTable :: Display a

  -- | Extract constructor name and children from Reified
  toNameAndChildren :: (forall t. FromDisplay t => Logic t var -> D)
                    -> Reified a var
                    -> (String, [D])

-- | Display a reified value using the display table
showReified :: forall a var. FromDisplay a
            => (forall t. FromDisplay t => Logic t var -> D)
            -> Reified a var -> D
showReified sh reified =
  let (name, children) = toNameAndChildren sh reified
  in case lookupDisplay name (displayTable @a) of
       Just f  -> f children
       Nothing -> Lit ("<" <> name <> ">")  -- fallback

instance FromDisplay Nat where
  displayTable = natDisplay

  toNameAndChildren _ ZR     = ("z", [])
  toNameAndChildren sh (SR n) = ("suc", [sh n])

instance FromDisplay Ty where
  displayTable = tyDisplay

  toNameAndChildren _ TUnitR        = ("tunit", [])
  toNameAndChildren sh (TArrR a b)  = ("tarr", [sh a, sh b])

instance FromDisplay Tm where
  displayTable = tmDisplay

  toNameAndChildren sh (VarR n)    = ("var", [sh n])
  toNameAndChildren _ UnitR        = ("unit", [])
  toNameAndChildren sh (LamR b)    = ("lam", [sh b])
  toNameAndChildren sh (AppR f x)  = ("app", [sh f, sh x])
  toNameAndChildren sh (AnnR e t)  = ("ann", [sh e, sh t])

--------------------------------------------------------------------------------
-- Display Functions
--------------------------------------------------------------------------------

-- | Display a logic term
showLogic :: FromDisplay a => Logic a var -> D
showLogic (Free _)   = Lit "?"
showLogic (Ground r) = showReified showLogic r

-- | Display a ground Haskell value
class FromDisplay a => ShowGround a where
  toReified :: a -> Reified a ()

instance ShowGround Nat where
  toReified Z     = ZR
  toReified (S n) = SR (Ground (toReified n))

instance ShowGround Ty where
  toReified TUnit      = TUnitR
  toReified (TArr a b) = TArrR (Ground (toReified a)) (Ground (toReified b))

instance ShowGround Tm where
  toReified (Var n)   = VarR (Ground (toReified n))
  toReified Unit      = UnitR
  toReified (Lam b)   = LamR (Ground (toReified b))
  toReified (App f x) = AppR (Ground (toReified f)) (Ground (toReified x))
  toReified (Ann e t) = AnnR (Ground (toReified e)) (Ground (toReified t))

-- | Pretty-print a ground value
prettyShow :: ShowGround a => a -> String
prettyShow = renderD . showReified showLogic . toReified

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

-- >>> prettyShow (S (S Z))
-- "S S 0"
--
-- >>> prettyShow (TArr TUnit TUnit)
-- "Unit → Unit"
--
-- >>> prettyShow (App (Lam (Var Z)) Unit)
-- "λ. var 0 ()"
--
-- >>> prettyShow (Ann (Lam (Var Z)) (TArr TUnit TUnit))
-- "λ. var 0 : Unit → Unit"

test :: IO ()
test = do
  putStrLn $ prettyShow (S (S Z))
  putStrLn $ prettyShow (TArr TUnit TUnit)
  putStrLn $ prettyShow (App (Lam (Var Z)) Unit)
  putStrLn $ prettyShow (Ann (Lam (Var Z)) (TArr TUnit TUnit))
