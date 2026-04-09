module LCTI.Main
  ( main
  , Expectation(..)
  , TestCase(..)
  , testCases
  , preEnv
  ) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Core.Term (ground)
import TypedRedex.Nominal (swap)
import TypedRedex.Nominal.Prelude (Nom(..), TyNom(..))
import TypedRedex.Nominal.Bind (Bind(..))
import Prelude hiding (abs, fst, snd)

import LCTI.Rules (infer)
import LCTI.Syntax

--------------------------------------------------------------------------------
-- Test Infrastructure
--------------------------------------------------------------------------------

data Expectation
  = ExpectFail
  | ExpectTy Ty
  deriving (Show)

data TestResult
  = TestPass String Ty
  | TestFail String
  | TestUnexpectedPass String [Ty]
  | TestUnexpectedFail String Ty
  | TestTypeMismatch String Ty [Ty]
  deriving (Show)

data TestCase = TestCase
  { tcName :: String
  , tcTerm :: Tm
  , tcExpect :: Expectation
  }

alphaEqTy :: Ty -> Ty -> Bool
alphaEqTy ty1 ty2 =
  case (ty1, ty2) of
    (TInt, TInt) -> True
    (TBool, TBool) -> True
    (TVar a, TVar b) -> a == b
    (TArr a b, TArr a' b') -> alphaEqTy a a' && alphaEqTy b b'
    (TForall (Bind a t1), TForall (Bind b t2)) ->
      alphaEqTy t1 (swap b a t2)
    (TUncurry tys1 t1, TUncurry tys2 t2) ->
      length tys1 == length tys2
        && and (zipWith alphaEqTy tys1 tys2)
        && alphaEqTy t1 t2
    (TList a, TList b) -> alphaEqTy a b
    (TProd a b, TProd a' b') -> alphaEqTy a a' && alphaEqTy b b'
    (TST a b, TST a' b') -> alphaEqTy a a' && alphaEqTy b b'
    _ -> False

runTest :: TestCase -> TestResult
runTest tc =
  let q = query $ do
        ty <- qfresh
        pure (infer (ground preEnv) cempty (ground (tcTerm tc)) ty, ty)
      results = eval q
      name = tcName tc
  in case tcExpect tc of
       ExpectFail ->
         if null results
           then TestFail name
           else TestUnexpectedPass name results
       ExpectTy expected ->
         case results of
           [] -> TestUnexpectedFail name expected
           _ ->
             case filter (alphaEqTy expected) results of
               (ty:_) -> TestPass name ty
               [] -> TestTypeMismatch name expected results

printResult :: TestResult -> IO ()
printResult (TestPass name ty) =
  putStrLn $ "[ok] " ++ name ++ " => " ++ show ty
printResult (TestFail name) =
  putStrLn $ "[ok] " ++ name ++ " (expected fail)"
printResult (TestUnexpectedPass name tys) =
  putStrLn $ "[FAIL] " ++ name ++ " => UNEXPECTED PASS: " ++ show tys
printResult (TestUnexpectedFail name expected) =
  putStrLn $ "[FAIL] " ++ name ++ " => UNEXPECTED FAIL (expected " ++ show expected ++ ")"
printResult (TestTypeMismatch name expected actuals) =
  putStrLn $ "[FAIL] " ++ name ++ " => TYPE MISMATCH: expected " ++ show expected ++ ", got " ++ show actuals

isPass :: TestResult -> Bool
isPass (TestPass _ _) = True
isPass (TestFail _) = True
isPass _ = False

--------------------------------------------------------------------------------
-- Type variable names
--------------------------------------------------------------------------------

a0, b0 :: TyNom
a0 = TyNom 0
b0 = TyNom 1

--------------------------------------------------------------------------------
-- Term variable names
--------------------------------------------------------------------------------

x0, y0, f0 :: Nom
x0 = Nom 0
y0 = Nom 1
f0 = Nom 3

--------------------------------------------------------------------------------
-- Helper to build forall types
--------------------------------------------------------------------------------

mkForall :: TyNom -> Ty -> Ty
mkForall a ty = TForall (Bind a ty)

--------------------------------------------------------------------------------
-- Standard library types (from original preEnvStrings)
--------------------------------------------------------------------------------

-- id : forall a. a -> a
idTy :: Ty
idTy = mkForall a0 (TArr (TVar a0) (TVar a0))

-- choose : forall a. a -> a -> a
chooseTy :: Ty
chooseTy = mkForall a0 (TArr (TVar a0) (TArr (TVar a0) (TVar a0)))

-- ids : [forall a. a -> a]
idsTy :: Ty
idsTy = TList (mkForall a0 (TArr (TVar a0) (TVar a0)))

-- auto : (forall a. a -> a) -> (forall a. a -> a)
autoTy :: Ty
autoTy = TArr (mkForall a0 (TArr (TVar a0) (TVar a0)))
              (mkForall a0 (TArr (TVar a0) (TVar a0)))

-- auto' : forall a. (forall b. b -> b) -> a -> a
auto'Ty :: Ty
auto'Ty = mkForall a0 (TArr (mkForall b0 (TArr (TVar b0) (TVar b0)))
                            (TArr (TVar a0) (TVar a0)))

-- poly : (forall a. a -> a) -> int * bool
polyTy :: Ty
polyTy = TArr (mkForall a0 (TArr (TVar a0) (TVar a0)))
              (TProd TInt TBool)

-- head : forall a. [a] -> a
headTy :: Ty
headTy = mkForall a0 (TArr (TList (TVar a0)) (TVar a0))

-- tail : forall a. [a] -> [a]
tailTy :: Ty
tailTy = mkForall a0 (TArr (TList (TVar a0)) (TList (TVar a0)))

-- length : forall a. [a] -> int
lengthTy :: Ty
lengthTy = mkForall a0 (TArr (TList (TVar a0)) TInt)

-- single : forall a. a -> [a]
singleTy :: Ty
singleTy = mkForall a0 (TArr (TVar a0) (TList (TVar a0)))

-- inc : int -> int
incTy :: Ty
incTy = TArr TInt TInt

-- append : forall a. [a] -> [a] -> [a]
appendTy :: Ty
appendTy = mkForall a0 (TArr (TList (TVar a0)) (TArr (TList (TVar a0)) (TList (TVar a0))))

-- map : forall a. forall b. (a -> b) -> [a] -> [b]
mapTy :: Ty
mapTy = mkForall a0 (mkForall b0 (TArr (TArr (TVar a0) (TVar b0))
                                       (TArr (TList (TVar a0)) (TList (TVar b0)))))

-- app : forall a. forall b. (a -> b) -> a -> b
appTy :: Ty
appTy = mkForall a0 (mkForall b0 (TArr (TArr (TVar a0) (TVar b0))
                                       (TArr (TVar a0) (TVar b0))))

-- revapp : forall a. forall b. a -> (a -> b) -> b
revappTy :: Ty
revappTy = mkForall a0 (mkForall b0 (TArr (TVar a0)
                                          (TArr (TArr (TVar a0) (TVar b0)) (TVar b0))))

-- runST : forall a. (forall b. ST b a) -> a
runSTTy :: Ty
runSTTy = mkForall a0 (TArr (mkForall b0 (TST (TVar b0) (TVar a0))) (TVar a0))

-- argST : forall a. ST a int
argSTTy :: Ty
argSTTy = mkForall a0 (TST (TVar a0) TInt)

-- f : forall a. (a -> a) -> [a] -> a
fTy :: Ty
fTy = mkForall a0 (TArr (TArr (TVar a0) (TVar a0))
                        (TArr (TList (TVar a0)) (TVar a0)))

-- h : int -> (forall a. a -> a)
hTy :: Ty
hTy = TArr TInt (mkForall a0 (TArr (TVar a0) (TVar a0)))

-- k : forall a. a -> [a] -> a
kTy :: Ty
kTy = mkForall a0 (TArr (TVar a0) (TArr (TList (TVar a0)) (TVar a0)))

-- lst : [forall a. int -> a -> a]
lstTy :: Ty
lstTy = TList (mkForall a0 (TArr TInt (TArr (TVar a0) (TVar a0))))

-- r : (forall a. a -> (forall b. b -> b)) -> int
rTy :: Ty
rTy = TArr (mkForall a0 (TArr (TVar a0) (mkForall b0 (TArr (TVar b0) (TVar b0))))) TInt

-- nil : forall a. [a]
nilTy :: Ty
nilTy = mkForall a0 (TList (TVar a0))

-- cons : forall a. a -> [a] -> [a]
consTy :: Ty
consTy = mkForall a0 (TArr (TVar a0) (TArr (TList (TVar a0)) (TList (TVar a0))))

-- fst : forall a. forall b. a * b -> a
fstTy :: Ty
fstTy = mkForall a0 (mkForall b0 (TArr (TProd (TVar a0) (TVar b0)) (TVar a0)))

-- snd : forall a. forall b. a * b -> b
sndTy :: Ty
sndTy = mkForall a0 (mkForall b0 (TArr (TProd (TVar a0) (TVar b0)) (TVar b0)))

-- st : forall a. forall b. a -> b -> ST a b
stTy :: Ty
stTy = mkForall a0 (mkForall b0 (TArr (TVar a0) (TArr (TVar b0) (TST (TVar a0) (TVar b0)))))

-- f1 : int * int
f1Ty :: Ty
f1Ty = TProd TInt TInt

-- f2 : (forall a. a -> a) * int
f2Ty :: Ty
f2Ty = TProd (mkForall a0 (TArr (TVar a0) (TVar a0))) TInt

--------------------------------------------------------------------------------
-- Uncurried standard library types
--------------------------------------------------------------------------------

-- id_uc : forall a. {a} -> a
idUcTy :: Ty
idUcTy = mkForall a0 (TUncurry [TVar a0] (TVar a0))

-- choose_uc : forall a. {a, a} -> a
chooseUcTy :: Ty
chooseUcTy = mkForall a0 (TUncurry [TVar a0, TVar a0] (TVar a0))

-- ids_uc : [forall a. {a} -> a]
idsUcTy :: Ty
idsUcTy = TList (mkForall a0 (TUncurry [TVar a0] (TVar a0)))

-- auto_uc : {forall a. {a} -> a} -> (forall a. {a} -> a)
autoUcTy :: Ty
autoUcTy = TUncurry [mkForall a0 (TUncurry [TVar a0] (TVar a0))]
                     (mkForall a0 (TUncurry [TVar a0] (TVar a0)))

-- auto'_uc : forall a. {forall b. {b} -> b} -> {a} -> a
auto'UcTy :: Ty
auto'UcTy =
  mkForall a0
    (TUncurry [mkForall b0 (TUncurry [TVar b0] (TVar b0))]
              (TUncurry [TVar a0] (TVar a0)))

-- poly_uc : {forall a. {a} -> a} -> int * bool
polyUcTy :: Ty
polyUcTy = TUncurry [mkForall a0 (TUncurry [TVar a0] (TVar a0))] (TProd TInt TBool)

-- head_uc : forall a. {[a]} -> a
headUcTy :: Ty
headUcTy = mkForall a0 (TUncurry [TList (TVar a0)] (TVar a0))

-- tail_uc : forall a. {[a]} -> [a]
tailUcTy :: Ty
tailUcTy = mkForall a0 (TUncurry [TList (TVar a0)] (TList (TVar a0)))

-- length_uc : forall a. {[a]} -> int
lengthUcTy :: Ty
lengthUcTy = mkForall a0 (TUncurry [TList (TVar a0)] TInt)

-- single_uc : forall a. {a} -> [a]
singleUcTy :: Ty
singleUcTy = mkForall a0 (TUncurry [TVar a0] (TList (TVar a0)))

-- inc_uc : {int} -> int
incUcTy :: Ty
incUcTy = TUncurry [TInt] TInt

-- append_uc : forall a. {[a], [a]} -> [a]
appendUcTy :: Ty
appendUcTy =
  mkForall a0
    (TUncurry [TList (TVar a0), TList (TVar a0)] (TList (TVar a0)))

-- map_uc : forall a. forall b. {{a} -> b, [a]} -> [b]
mapUcTy :: Ty
mapUcTy =
  mkForall a0
    (mkForall b0
      (TUncurry [TUncurry [TVar a0] (TVar b0), TList (TVar a0)] (TList (TVar b0))))

-- app_uc : forall a. forall b. {{a} -> b, a} -> b
appUcTy :: Ty
appUcTy =
  mkForall a0
    (mkForall b0
      (TUncurry [TUncurry [TVar a0] (TVar b0), TVar a0] (TVar b0)))

-- revapp_uc : forall a. forall b. {a, {a} -> b} -> b
revappUcTy :: Ty
revappUcTy =
  mkForall a0
    (mkForall b0
      (TUncurry [TVar a0, TUncurry [TVar a0] (TVar b0)] (TVar b0)))

-- runST_uc : forall a. {forall b. ST b a} -> a
runSTUcTy :: Ty
runSTUcTy =
  mkForall a0 (TUncurry [mkForall b0 (TST (TVar b0) (TVar a0))] (TVar a0))

-- argST_uc : forall a. ST a int
argSTUcTy :: Ty
argSTUcTy = argSTTy

-- f_uc : forall a. {{a} -> a, [a]} -> a
fUcTy :: Ty
fUcTy =
  mkForall a0 (TUncurry [TUncurry [TVar a0] (TVar a0), TList (TVar a0)] (TVar a0))

-- h_uc : {int} -> (forall a. {a} -> a)
hUcTy :: Ty
hUcTy = TUncurry [TInt] (mkForall a0 (TUncurry [TVar a0] (TVar a0)))

-- k_uc : forall a. {a} -> {[a]} -> a
kUcTy :: Ty
kUcTy =
  mkForall a0 (TUncurry [TVar a0] (TUncurry [TList (TVar a0)] (TVar a0)))

-- lst_uc : [forall a. {int} -> {a} -> a]
lstUcTy :: Ty
lstUcTy =
  TList (mkForall a0 (TUncurry [TInt] (TUncurry [TVar a0] (TVar a0))))

-- r_uc : {forall a. {a} -> (forall b. {b} -> b)} -> int
rUcTy :: Ty
rUcTy =
  TUncurry
    [mkForall a0 (TUncurry [TVar a0] (mkForall b0 (TUncurry [TVar b0] (TVar b0))))]
    TInt

-- cons_uc : forall a. {a, [a]} -> [a]
consUcTy :: Ty
consUcTy =
  mkForall a0 (TUncurry [TVar a0, TList (TVar a0)] (TList (TVar a0)))

-- fst_uc : forall a. forall b. {a * b} -> a
fstUcTy :: Ty
fstUcTy =
  mkForall a0 (mkForall b0 (TUncurry [TProd (TVar a0) (TVar b0)] (TVar a0)))

-- snd_uc : forall a. forall b. {a * b} -> b
sndUcTy :: Ty
sndUcTy =
  mkForall a0 (mkForall b0 (TUncurry [TProd (TVar a0) (TVar b0)] (TVar b0)))

-- st_uc : forall a. forall b. {a, b} -> ST a b
stUcTy :: Ty
stUcTy =
  mkForall a0 (mkForall b0 (TUncurry [TVar a0, TVar b0] (TST (TVar a0) (TVar b0))))

--------------------------------------------------------------------------------
-- Pre-environment
--------------------------------------------------------------------------------

idN, chooseN, idsN, autoN, auto'N, polyN, headN, tailN, lengthN, singleN :: Nom
incN, appendN, mapN, appN, revappN, runSTN, argSTN, fN, hN, kN, lstN, rN :: Nom
nilN, consN, fstN, sndN, f1N, f2N, stN :: Nom
idN = Nom 10
chooseN = Nom 11
idsN = Nom 12
autoN = Nom 13
auto'N = Nom 14
polyN = Nom 15
headN = Nom 16
tailN = Nom 17
lengthN = Nom 18
singleN = Nom 19
incN = Nom 20
appendN = Nom 21
mapN = Nom 22
appN = Nom 23
revappN = Nom 24
runSTN = Nom 25
argSTN = Nom 26
fN = Nom 27
hN = Nom 28
kN = Nom 29
lstN = Nom 30
rN = Nom 31
nilN = Nom 32
consN = Nom 33
fstN = Nom 34
sndN = Nom 35
f1N = Nom 36
f2N = Nom 37
stN = Nom 38

idUcN, chooseUcN, idsUcN, autoUcN, auto'UcN, polyUcN, headUcN, tailUcN, lengthUcN :: Nom
singleUcN, incUcN, appendUcN, mapUcN, appUcN, revappUcN, runSTUcN, argSTUcN :: Nom
fUcN, hUcN, kUcN, lstUcN, rUcN, consUcN, fstUcN, sndUcN, stUcN :: Nom
idUcN = Nom 110
chooseUcN = Nom 111
idsUcN = Nom 112
autoUcN = Nom 113
auto'UcN = Nom 114
polyUcN = Nom 115
headUcN = Nom 116
tailUcN = Nom 117
lengthUcN = Nom 118
singleUcN = Nom 119
incUcN = Nom 120
appendUcN = Nom 121
mapUcN = Nom 122
appUcN = Nom 123
revappUcN = Nom 124
runSTUcN = Nom 125
argSTUcN = Nom 126
fUcN = Nom 127
hUcN = Nom 128
kUcN = Nom 129
lstUcN = Nom 130
rUcN = Nom 131
consUcN = Nom 132
fstUcN = Nom 133
sndUcN = Nom 134
stUcN = Nom 135

preEnvEntries :: [(Nom, Ty)]
preEnvEntries =
  [ (idN, idTy)
  , (chooseN, chooseTy)
  , (idsN, idsTy)
  , (autoN, autoTy)
  , (auto'N, auto'Ty)
  , (polyN, polyTy)
  , (headN, headTy)
  , (tailN, tailTy)
  , (lengthN, lengthTy)
  , (singleN, singleTy)
  , (incN, incTy)
  , (appendN, appendTy)
  , (mapN, mapTy)
  , (appN, appTy)
  , (revappN, revappTy)
  , (runSTN, runSTTy)
  , (argSTN, argSTTy)
  , (fN, fTy)
  , (hN, hTy)
  , (kN, kTy)
  , (lstN, lstTy)
  , (rN, rTy)
  , (nilN, nilTy)
  , (consN, consTy)
  , (fstN, fstTy)
  , (sndN, sndTy)
  , (stN, stTy)
  , (f1N, f1Ty)
  , (f2N, f2Ty)
  , (idUcN, idUcTy)
  , (chooseUcN, chooseUcTy)
  , (idsUcN, idsUcTy)
  , (autoUcN, autoUcTy)
  , (auto'UcN, auto'UcTy)
  , (polyUcN, polyUcTy)
  , (headUcN, headUcTy)
  , (tailUcN, tailUcTy)
  , (lengthUcN, lengthUcTy)
  , (singleUcN, singleUcTy)
  , (incUcN, incUcTy)
  , (appendUcN, appendUcTy)
  , (mapUcN, mapUcTy)
  , (appUcN, appUcTy)
  , (revappUcN, revappUcTy)
  , (runSTUcN, runSTUcTy)
  , (argSTUcN, argSTUcTy)
  , (fUcN, fUcTy)
  , (hUcN, hUcTy)
  , (kUcN, kUcTy)
  , (lstUcN, lstUcTy)
  , (rUcN, rUcTy)
  , (consUcN, consUcTy)
  , (fstUcN, fstUcTy)
  , (sndUcN, sndUcTy)
  , (stUcN, stUcTy)
  ]

preEnv :: Env
preEnv = foldr (uncurry ETrm) EEmpty preEnvEntries

-- Variable references
idV, chooseV, idsV, autoV, auto'V, polyV, headV, tailV, lengthV, singleV :: Tm
incV, appendV, mapV, appV, revappV, runSTV, argSTV, fV, hV, kV, lstV, rV :: Tm
nilV, consV, fstV, f1V, f2V :: Tm
idUcV, chooseUcV, idsUcV, autoUcV, auto'UcV, polyUcV, headUcV, tailUcV, lengthUcV :: Tm
singleUcV, incUcV, appendUcV, mapUcV, appUcV, revappUcV, runSTUcV, argSTUcV :: Tm
hUcV, kUcV, lstUcV, rUcV, consUcV :: Tm
idV = Var idN
chooseV = Var chooseN
idsV = Var idsN
autoV = Var autoN
auto'V = Var auto'N
polyV = Var polyN
headV = Var headN
tailV = Var tailN
lengthV = Var lengthN
singleV = Var singleN
incV = Var incN
appendV = Var appendN
mapV = Var mapN
appV = Var appN
revappV = Var revappN
runSTV = Var runSTN
argSTV = Var argSTN
fV = Var fN
hV = Var hN
kV = Var kN
lstV = Var lstN
rV = Var rN
nilV = Var nilN
consV = Var consN
fstV = Var fstN
f1V = Var f1N
f2V = Var f2N
idUcV = Var idUcN
chooseUcV = Var chooseUcN
idsUcV = Var idsUcN
autoUcV = Var autoUcN
auto'UcV = Var auto'UcN
polyUcV = Var polyUcN
headUcV = Var headUcN
tailUcV = Var tailUcN
lengthUcV = Var lengthUcN
singleUcV = Var singleUcN
incUcV = Var incUcN
appendUcV = Var appendUcN
mapUcV = Var mapUcN
appUcV = Var appUcN
revappUcV = Var revappUcN
runSTUcV = Var runSTUcN
argSTUcV = Var argSTUcN
hUcV = Var hUcN
kUcV = Var kUcN
lstUcV = Var lstUcN
rUcV = Var rUcN
consUcV = Var consUcN

--------------------------------------------------------------------------------
-- Helper functions for building terms
--------------------------------------------------------------------------------

mkAbs :: Nom -> Tm -> Tm
mkAbs x body = Abs (Bind x body)

mkAbsAnn :: Nom -> Ty -> Tm -> Tm
mkAbsAnn x ty body = AbsAnn (Bind (x, ty) body)

mkAbsUncurry :: [Nom] -> Tm -> Tm
mkAbsUncurry xs body = AbsUncurry (Bind xs body)

mkAbsUncurryAnn :: [(Nom, Ty)] -> Tm -> Tm
mkAbsUncurryAnn xs body = AbsUncurryAnn (Bind xs body)

mkTAbs :: TyNom -> Tm -> Tm
mkTAbs a body = TAbs (Bind a body)

app2 :: Tm -> Tm -> Tm -> Tm
app2 f a b = App (App f a) b

appU1 :: Tm -> Tm -> Tm
appU1 f a = AppUncurry f [a]

appU2 :: Tm -> Tm -> Tm -> Tm
appU2 f a b = AppUncurry f [a, b]

passCase :: String -> Tm -> Ty -> TestCase
passCase name tm ty = TestCase name tm (ExpectTy ty)

failCase :: String -> Tm -> TestCase
failCase name tm = TestCase name tm ExpectFail

--------------------------------------------------------------------------------
-- Test Cases (matching original Tests.txt results)
-- Pass/Fail expectations are based on original implementation behavior
--------------------------------------------------------------------------------

testCases :: [TestCase]
testCases =
  [ -- ===== A Series =====
    failCase "A1" (mkAbs x0 (mkAbs y0 (Var y0)))
  , passCase "A1 (Fc translation 1)"
      (mkTAbs a0 (mkTAbs b0 (Ann (mkAbs x0 (mkAbs y0 (Var y0)))
                                  (TArr (TVar a0) (TArr (TVar b0) (TVar b0))))))
      (mkForall a0 (mkForall b0 (TArr (TVar a0) (TArr (TVar b0) (TVar b0)))))
  , passCase "A1 (Fc translation 1, uncurried)"
      (mkTAbs a0 (mkTAbs b0 (Ann (mkAbsUncurry [x0, y0] (Var y0))
                                  (TUncurry [TVar a0, TVar b0] (TVar b0)))))
      (mkForall a0 (mkForall b0 (TUncurry [TVar a0, TVar b0] (TVar b0))))
  , passCase "A1 (Fc translation 2)"
      (mkTAbs a0 (mkTAbs b0 (mkAbsAnn x0 (TVar a0) (mkAbsAnn y0 (TVar b0) (Var y0)))))
      (mkForall a0 (mkForall b0 (TArr (TVar a0) (TArr (TVar b0) (TVar b0)))))
  , passCase "A1 (Fc translation 2, uncurried)"
      (mkTAbs a0 (mkTAbs b0 (mkAbsUncurryAnn [(x0, TVar a0), (y0, TVar b0)] (Var y0))))
      (mkForall a0 (mkForall b0 (TUncurry [TVar a0, TVar b0] (TVar b0))))
  , failCase "A1 (uncurried)" (mkAbsUncurry [x0, y0] (Var y0))
  , passCase "A2" (App chooseV idV) (TArr idTy idTy)
  , passCase "A2 (uncurried)" (appU1 chooseUcV idUcV) idUcTy
  , failCase "A3" (app2 chooseV nilV idsV)
  , passCase "A3 (Fc translation)" (app2 chooseV (Ann Nil idsTy) idsV) idsTy
  , failCase "A3 (uncurried)" (appU2 chooseUcV Nil idsUcV)
  , passCase "A3 (Fc translation, uncurried)" (appU2 chooseUcV (Ann Nil idsUcTy) idsUcV) idsUcTy
  , failCase "A4" (mkAbs x0 (App (Var x0) (Var x0)))
  , passCase "A4 (Fc translation 1)"
      (Ann (mkAbs x0 (App (Var x0) (Var x0))) autoTy)
      autoTy
  , passCase "A4 (Fc translation 2)"
      (mkAbsAnn x0 idTy (App (Var x0) (Var x0)))
      autoTy
  , failCase "A4 (uncurried)" (mkAbsUncurry [x0] (appU1 (Var x0) (Var x0)))
  , passCase "A4 (Fc translation 1, uncurried)"
      (Ann (mkAbsUncurry [x0] (appU1 (Var x0) (Var x0))) autoUcTy)
      autoUcTy
  , passCase "A4 (Fc translation 2, uncurried)"
      (mkAbsUncurryAnn [(x0, idUcTy)] (appU1 (Var x0) (Var x0)))
      autoUcTy
  , passCase "A5" (App idV autoV) autoTy
  , passCase "A5 (uncurried)" (appU1 idUcV autoUcV) autoUcTy
  , passCase "A6" (App idV auto'V) auto'Ty
  , passCase "A6 (uncurried)" (appU1 idUcV auto'UcV) auto'UcTy
  , failCase "A7" (app2 chooseV idV autoV)
  , passCase "A7 (Fc translation)" (app2 chooseV (TApp idV idTy) autoV) autoTy
  , failCase "A7 (uncurried)" (appU2 chooseUcV idUcV autoUcV)
  , passCase "A7 (Fc translation, uncurried)" (appU2 chooseUcV (TApp idUcV idUcTy) autoUcV) autoUcTy
  , failCase "A8" (app2 chooseV idV auto'V)
  , passCase "A8 (Fc translation 1)"
      (app2 chooseV
        (mkTAbs a0
          (Ann (mkAbs f0 (TApp (App idV (Var f0)) (TVar a0)))
               (TArr (mkForall b0 (TArr (TVar b0) (TVar b0)))
                     (TArr (TVar a0) (TVar a0)))))
        auto'V)
      auto'Ty
  , passCase "A8 (Fc translation 2)"
      (app2 chooseV
        (mkTAbs a0
          (Ann (mkAbs f0 (mkAbs x0 (App (App idV (Var f0)) (Var x0))))
               (TArr (mkForall b0 (TArr (TVar b0) (TVar b0)))
                     (TArr (TVar a0) (TVar a0)))))
        auto'V)
      auto'Ty
  , passCase "A8 (Fc translation 3)"
      (app2 chooseV
        (mkTAbs a0
          (mkAbsAnn f0 (mkForall b0 (TArr (TVar b0) (TVar b0)))
            (TApp (App idV (Var f0)) (TVar a0))))
        auto'V)
      auto'Ty
  , failCase "A8 (uncurried)" (appU2 chooseUcV idUcV auto'UcV)
  , passCase "A8 (Fc translation 1, uncurried)"
      (appU2 chooseUcV
        (mkTAbs a0
          (Ann (mkAbsUncurry [f0] (appU1 idUcV (TApp (Var f0) (TVar a0))))
               (TUncurry [mkForall b0 (TUncurry [TVar b0] (TVar b0))]
                         (TUncurry [TVar a0] (TVar a0)))))
        auto'UcV)
      auto'UcTy
  , passCase "A8 (Fc translation 2, uncurried)"
      (appU2 chooseUcV
        (mkTAbs a0
          (Ann (mkAbsUncurry [f0]
                 (mkAbsUncurry [x0] (appU1 (appU1 idUcV (Var f0)) (Var x0))))
               (TUncurry [mkForall b0 (TUncurry [TVar b0] (TVar b0))]
                         (TUncurry [TVar a0] (TVar a0)))))
        auto'UcV)
      auto'UcTy
  , passCase "A8 (Fc translation 3, uncurried)"
      (appU2 chooseUcV
        (mkTAbs a0
          (mkAbsUncurryAnn [(f0, mkForall b0 (TUncurry [TVar b0] (TVar b0)))]
            (appU1 idUcV (TApp (Var f0) (TVar a0)))))
        auto'UcV)
      auto'UcTy
  , passCase "A9" (app2 fV (App chooseV idV) idsV) idTy
  , passCase "A10" (App polyV idV) (TProd TInt TBool)
  , passCase "A10 (uncurried)" (appU1 polyUcV idUcV) (TProd TInt TBool)
  , failCase "A11" (App polyV (mkAbs x0 (Var x0)))
  , passCase "A11 (Fc translation)" (App polyV (mkTAbs a0 (mkAbs x0 (Var x0)))) (TProd TInt TBool)
  , failCase "A11 (uncurried)" (appU1 polyUcV (mkAbsUncurry [x0] (Var x0)))
  , passCase "A11 (Fc translation, uncurried)"
      (appU1 polyUcV (mkTAbs a0 (mkAbsUncurry [x0] (Var x0))))
      (TProd TInt TBool)
  , failCase "A12" (app2 idV polyV (mkAbs x0 (Var x0)))
  , passCase "A12 (Fc translation)"
      (app2 idV polyV (mkTAbs a0 (mkAbs x0 (Var x0))))
      (TProd TInt TBool)
  , failCase "A12 (uncurried)"
      (appU1 (appU1 idUcV polyUcV) (mkAbsUncurry [x0] (Var x0)))
  , passCase "A12 (Fc translation, uncurried)"
      (appU1 (appU1 idUcV polyUcV) (mkTAbs a0 (mkAbsUncurry [x0] (Var x0))))
      (TProd TInt TBool)

    -- ===== B Series =====
  , failCase "B1" (mkAbs f0 (Pair (App (Var f0) (LitInt 1)) (App (Var f0) (LitBool True))))
  , passCase "B1 (Fc translation 1)"
      (Ann (mkAbs f0 (Pair (App (Var f0) (LitInt 1)) (App (Var f0) (LitBool True)))) polyTy)
      polyTy
  , passCase "B1 (Fc translation 2)"
      (mkAbsAnn f0 idTy (Pair (App (Var f0) (LitInt 1)) (App (Var f0) (LitBool True))))
      polyTy
  , failCase "B1 (uncurried)"
      (mkAbsUncurry [f0] (Pair (App (Var f0) (LitInt 1)) (App (Var f0) (LitBool True))))
  , passCase "B1 (Fc translation 1, uncurried)"
      (Ann (mkAbsUncurry [f0]
             (Pair (appU1 (Var f0) (LitInt 1)) (appU1 (Var f0) (LitBool True))))
           polyUcTy)
      polyUcTy
  , passCase "B1 (Fc translation 2, uncurried)"
      (mkAbsUncurryAnn [(f0, idUcTy)]
        (Pair (appU1 (Var f0) (LitInt 1)) (appU1 (Var f0) (LitBool True))))
      polyUcTy
  , failCase "B2" (mkAbs x0 (App polyV (App headV (Var x0))))
  , passCase "B2 (Fc translation 1)"
      (Ann (mkAbs x0 (App polyV (App headV (Var x0))))
           (TArr idsTy (TProd TInt TBool)))
      (TArr idsTy (TProd TInt TBool))
  , passCase "B2 (Fc translation 2)"
      (mkAbsAnn x0 idsTy (App polyV (App headV (Var x0))))
      (TArr idsTy (TProd TInt TBool))
  , failCase "B2 (uncurried)"
      (mkAbsUncurry [x0] (appU1 polyUcV (appU1 headUcV (Var x0))))
  , passCase "B2 (Fc translation 1, uncurried)"
      (Ann (mkAbsUncurry [x0] (appU1 polyUcV (appU1 headUcV (Var x0))))
           (TUncurry [idsUcTy] (TProd TInt TBool)))
      (TUncurry [idsUcTy] (TProd TInt TBool))
  , passCase "B2 (Fc translation 2, uncurried)"
      (mkAbsUncurryAnn [(x0, idsUcTy)]
        (appU1 polyUcV (appU1 headUcV (Var x0))))
      (TUncurry [idsUcTy] (TProd TInt TBool))

    -- ===== C Series =====
  , passCase "C1" (App lengthV idsV) TInt
  , passCase "C1 (uncurried)" (appU1 lengthUcV idsUcV) TInt
  , passCase "C2" (App tailV idsV) idsTy
  , passCase "C2 (uncurried)" (appU1 tailUcV idsUcV) idsUcTy
  , passCase "C3" (App headV idsV) idTy
  , passCase "C3 (uncurried)" (appU1 headUcV idsUcV) idUcTy
  , passCase "C4" (App singleV idV) idsTy
  , passCase "C4 (uncurried)" (appU1 singleUcV idUcV) idsUcTy
  , passCase "C5" (app2 consV idV idsV) idsTy
  , passCase "C5 (uncurried)" (appU2 consUcV idUcV idsUcV) idsUcTy
  , failCase "C6" (app2 consV (mkAbs x0 (Var x0)) idsV)
  , passCase "C6 (Fc translation 1)"
      (app2 consV (mkTAbs a0 (Ann (mkAbs x0 (Var x0)) (TArr (TVar a0) (TVar a0)))) idsV)
      idsTy
  , passCase "C6 (Fc translation 2)"
      (app2 consV (mkTAbs a0 (mkAbsAnn x0 (TVar a0) (Var x0))) idsV)
      idsTy
  , failCase "C6 (uncurried)" (appU2 consUcV (mkAbsUncurry [x0] (Var x0)) idsUcV)
  , passCase "C6 (Fc translation 1, uncurried)"
      (appU2 consUcV
        (mkTAbs a0 (Ann (mkAbsUncurry [x0] (Var x0)) (TUncurry [TVar a0] (TVar a0))))
        idsUcV)
      idsUcTy
  , passCase "C6 (Fc translation 2, uncurried)"
      (appU2 consUcV
        (mkTAbs a0 (mkAbsUncurryAnn [(x0, TVar a0)] (Var x0)))
        idsUcV)
      idsUcTy
  , failCase "C7" (app2 appendV (App singleV incV) (App singleV idV))
  , passCase "C7 (Fc translation)"
      (app2 appendV (App singleV incV) (App singleV (TApp idV TInt)))
      (TList (TArr TInt TInt))
  , failCase "C7 (uncurried)"
      (appU2 appendUcV (appU1 singleUcV incUcV) (appU1 singleUcV idUcV))
  , passCase "C7 (Fc translation, uncurried)"
      (appU2 appendUcV (appU1 singleUcV incUcV) (appU1 singleUcV (TApp idUcV TInt)))
      (TList (TUncurry [TInt] TInt))
  , passCase "C8" (app2 appendV (App singleV idV) idsV) idsTy
  , passCase "C8 (uncurried)" (appU2 appendUcV (appU1 singleUcV idUcV) idsUcV) idsUcTy
  , passCase "C9" (app2 mapV polyV (App singleV idV)) (TList (TProd TInt TBool))
  , passCase "C9 (uncurried)"
      (appU2 mapUcV polyUcV (appU1 singleUcV idUcV))
      (TList (TProd TInt TBool))
  , failCase "C10" (app2 mapV headV (App singleV idsV))
  , passCase "C10 (Fc translation)"
      (app2 mapV (TApp headV idTy) (App singleV idsV))
      idsTy
  , failCase "C10 (uncurried)" (appU2 mapUcV headUcV (appU1 singleUcV idsUcV))
  , passCase "C10 (Fc translation, uncurried)"
      (appU2 mapUcV (TApp headUcV idUcTy) (appU1 singleUcV idsUcV))
      idsUcTy

    -- ===== D Series =====
  , passCase "D1" (app2 appV polyV idV) (TProd TInt TBool)
  , passCase "D1 (uncurried)" (appU2 appUcV polyUcV idUcV) (TProd TInt TBool)
  , passCase "D2" (app2 revappV idV polyV) (TProd TInt TBool)
  , passCase "D2 (uncurried)" (appU2 revappUcV idUcV polyUcV) (TProd TInt TBool)
  , passCase "D3" (App runSTV argSTV) TInt
  , passCase "D3 (uncurried)" (appU1 runSTUcV argSTUcV) TInt
  , failCase "D4" (app2 appV runSTV argSTV)
  , passCase "D4 (Fc translation 1)"
      (app2 appV
        (Ann (mkAbs x0 (App runSTV (mkTAbs a0 (TApp (Var x0) (TVar a0)))))
             (TArr (mkForall a0 (TST (TVar a0) TInt)) TInt))
        argSTV)
      TInt
  , passCase "D4 (Fc translation 2)"
      (app2 appV
        (mkAbsAnn x0 (mkForall a0 (TST (TVar a0) TInt))
          (App runSTV (mkTAbs a0 (TApp (Var x0) (TVar a0)))))
        argSTV)
      TInt
  , passCase "D4 (Fc translation 3)" (app2 appV (TApp runSTV TInt) argSTV) TInt
  , failCase "D4 (uncurried)" (appU2 appUcV runSTUcV argSTUcV)
  , passCase "D4 (Fc translation 1, uncurried)"
      (appU2 appUcV
        (Ann (mkAbsUncurry [x0] (appU1 runSTUcV (mkTAbs a0 (TApp (Var x0) (TVar a0)))))
             (TUncurry [mkForall a0 (TST (TVar a0) TInt)] TInt))
        argSTUcV)
      TInt
  , passCase "D4 (Fc translation 2, uncurried)"
      (appU2 appUcV
        (mkAbsUncurryAnn [(x0, mkForall a0 (TST (TVar a0) TInt))]
          (appU1 runSTUcV (mkTAbs a0 (TApp (Var x0) (TVar a0)))))
        argSTUcV)
      TInt
  , passCase "D4 (Fc translation 3, uncurried)" (appU2 appUcV (TApp runSTUcV TInt) argSTUcV) TInt
  , failCase "D5" (app2 revappV argSTV runSTV)
  , passCase "D5 (Fc translation 1)" (app2 revappV argSTV (TApp runSTV TInt)) TInt
  , passCase "D5 (Fc translation 2)"
      (app2 revappV argSTV
        (Ann (mkAbs x0 (App runSTV (mkTAbs a0 (TApp (Var x0) (TVar a0)))))
             (TArr (mkForall a0 (TST (TVar a0) TInt)) TInt)))
      TInt
  , failCase "D5 (uncurried)" (appU2 revappUcV argSTUcV runSTUcV)
  , passCase "D5 (Fc translation 1, uncurried)" (appU2 revappUcV argSTUcV (TApp runSTUcV TInt)) TInt
  , passCase "D5 (Fc translation 2, uncurried)"
      (appU2 revappUcV argSTUcV
        (Ann (mkAbsUncurry [x0] (appU1 runSTUcV (mkTAbs a0 (TApp (Var x0) (TVar a0)))))
             (TUncurry [mkForall a0 (TST (TVar a0) TInt)] TInt)))
      TInt

    -- ===== E Series =====
  , failCase "E1" (app2 kV hV lstV)
  , failCase "E1 (uncurried)" (appU1 (appU1 kUcV hUcV) lstUcV)
  , failCase "E2" (app2 kV (mkAbs x0 (App hV (Var x0))) lstV)
  , passCase "E2 (Fc translation 1)"
      (app2 kV
        (mkTAbs a0
          (Ann (mkAbs x0 (TApp (App hV (Var x0)) (TVar a0)))
               (TArr TInt (TArr (TVar a0) (TVar a0)))))
        lstV)
      (mkForall a0 (TArr TInt (TArr (TVar a0) (TVar a0))))
  , passCase "E2 (Fc translation 2)"
      (app2 kV
        (mkTAbs a0
          (mkAbsAnn x0 TInt (TApp (App hV (Var x0)) (TVar a0))))
        lstV)
      (mkForall a0 (TArr TInt (TArr (TVar a0) (TVar a0))))
  , failCase "E2 (uncurried)"
      (appU1 (appU1 kUcV (mkAbsUncurry [x0] (appU1 hUcV (Var x0)))) lstUcV)
  , passCase "E2 (Fc translation 1, uncurried)"
      (appU1
        (appU1 kUcV
          (mkTAbs a0
            (Ann (mkAbsUncurry [x0] (TApp (appU1 hUcV (Var x0)) (TVar a0)))
                 (TUncurry [TInt] (TUncurry [TVar a0] (TVar a0))))))
        lstUcV)
      (mkForall a0 (TUncurry [TInt] (TUncurry [TVar a0] (TVar a0))))
  , passCase "E2 (Fc translation 2, uncurried)"
      (appU1
        (appU1 kUcV
          (mkTAbs a0
            (mkAbsUncurryAnn [(x0, TInt)] (TApp (appU1 hUcV (Var x0)) (TVar a0)))))
        lstUcV)
      (mkForall a0 (TUncurry [TInt] (TUncurry [TVar a0] (TVar a0))))
  , failCase "E3" (App rV (mkAbs x0 (mkAbs y0 (Var y0))))
  , passCase "E3 (Fc translation 1)"
      (App rV
        (mkTAbs a0
          (Ann (mkAbs x0 (mkTAbs b0 (mkAbs y0 (Var y0))))
               (TArr (TVar a0) (mkForall b0 (TArr (TVar b0) (TVar b0)))))))
      TInt
  , passCase "E3 (Fc translation 2)"
      (App rV
        (mkTAbs a0
          (mkAbsAnn x0 (TVar a0) (mkTAbs b0 (mkAbsAnn y0 (TVar b0) (Var y0))))))
      TInt
  , failCase "E3 (uncurried)"
      (appU1 rUcV (mkAbsUncurry [x0] (mkAbsUncurry [y0] (Var y0))))
  , passCase "E3 (Fc translation 1, uncurried)"
      (appU1 rUcV
        (mkTAbs a0
          (Ann (mkAbsUncurry [x0] (mkTAbs b0 (mkAbsUncurry [y0] (Var y0))))
               (TUncurry [TVar a0] (mkForall b0 (TUncurry [TVar b0] (TVar b0)))))))
      TInt
  , passCase "E3 (Fc translation 2, uncurried)"
      (appU1 rUcV
        (mkTAbs a0
          (mkAbsUncurryAnn [(x0, TVar a0)] (mkTAbs b0 (mkAbsUncurryAnn [(y0, TVar b0)] (Var y0))))))
      TInt

    -- ===== F Series =====
  , passCase "F5" (App autoV idV) idTy
  , passCase "F5 (uncurried)" (appU1 autoUcV idUcV) idUcTy
  , passCase "F6" (app2 consV (App headV idsV) idsV) idsTy
  , passCase "F6 (uncurried)" (appU2 consUcV (appU1 headUcV idsUcV) idsUcV) idsUcTy
  , passCase "F7" (app2 headV idsV (LitInt 3)) TInt
  , passCase "F7 (uncurried)" (appU1 (appU1 headUcV idsUcV) (LitInt 3)) TInt
  , passCase "F8" (App chooseV (App headV idsV)) (TArr idTy idTy)

    -- ===== Pair and Const =====
  , passCase "Pair" (Ann (Pair (mkAbs x0 (Var x0)) (LitInt 1)) (TProd (TArr TInt TInt) TInt))
      (TProd (TArr TInt TInt) TInt)
  , passCase "Const"
      (app2
        (mkTAbs a0 (mkTAbs b0 (mkAbsAnn x0 (TVar a0) (mkAbsAnn y0 (TVar b0) (Var x0)))))
        (LitInt 1)
        (LitBool True))
      TInt
  , passCase "Const (uncurried)"
      (appU1
        (appU1
          (mkTAbs a0 (mkTAbs b0 (mkAbsUncurryAnn [(x0, TVar a0)] (mkAbsUncurryAnn [(y0, TVar b0)] (Var x0)))))
          (LitInt 1))
        (LitBool True))
      TInt
  , passCase "Pair0"
      (Ann (Fst (Pair (mkAbs x0 (Var x0)) (LitInt 2))) (TArr TInt TInt))
      (TArr TInt TInt)
  , passCase "Pair1" (App fstV f1V) TInt
  , passCase "Pair2" (app2 fstV f2V (LitInt 1)) TInt
  , passCase "Pair3" (app2 fstV (Pair idV (LitInt 1)) (LitInt 1)) TInt
  ]

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== LCTI Type Inference Tests ==="
  putStrLn ""

  let results = map runTest testCases
  mapM_ printResult results

  putStrLn ""
  putStrLn "=== Summary ==="
  let total = length results
      passed = length (filter isPass results)
      failed = total - passed
  putStrLn $ "Total: " ++ show total
  putStrLn $ "Passed: " ++ show passed
  putStrLn $ "Failed: " ++ show failed

  if failed > 0
    then do
      putStrLn ""
      putStrLn "Failed tests:"
      mapM_ (\r -> case r of
                     TestUnexpectedPass n _ -> putStrLn $ "  - " ++ n ++ " (UNEXPECTED PASS)"
                     TestUnexpectedFail n _ -> putStrLn $ "  - " ++ n ++ " (UNEXPECTED FAIL)"
                     TestTypeMismatch n _ _ -> putStrLn $ "  - " ++ n ++ " (TYPE MISMATCH)"
                     _ -> pure ()) results
    else putStrLn "All tests passed!"
