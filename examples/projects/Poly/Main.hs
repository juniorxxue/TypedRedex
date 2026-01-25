module Poly.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)
import TypedRedex.Nominal.Prelude (nom, tynom)

import Poly.Rules (infer, ssub, sub)
import Poly.Syntax
import Support.Nat (zro, suc)

assertNonEmpty :: Show a => String -> [a] -> IO ()
assertNonEmpty name xs =
  if null xs
    then error ("[fail] " ++ name ++ ": expected results, got " ++ show xs)
    else putStrLn ("[ok] " ++ name)

assertEmpty :: Show a => String -> [a] -> IO ()
assertEmpty name xs =
  if null xs
    then putStrLn ("[ok] " ++ name)
    else error ("[fail] " ++ name ++ ": expected no results, got " ++ show xs)

printTrace :: String -> [TraceResult a] -> IO ()
printTrace name results =
  case results of
    TraceOk _ deriv : _ -> do
      putStrLn ("--- trace " ++ name ++ " ---")
      putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> do
      putStrLn ("--- trace " ++ name ++ " (failed) ---")
      putStrLn (prettyDerivation deriv)
    [] -> putStrLn ("--- trace " ++ name ++ " (no results) ---")

main :: IO ()
main = do
  putStrLn "=== Poly ==="
  putStrLn ""
  putStrLn (typeset ssub)
  putStrLn (typeset sub)
  putStrLn (typeset infer)

  let one = suc zro
      x0 = nom 0
      a0 = tynom 0
      idLam = lam x0 (var x0)
      idAnn = ann idLam (tarr tint tint)
      idApp = app idAnn (lit one)
      idAppUnann = app idLam (lit one)

--   -- Test 1: infer eempty cempty (lit 1)
--   let q1 = query $ do
--         ty <- qfresh
--         env <- qfresh
--         pure (infer eempty cempty (lit one) ty env, (ty, env))
--   printTrace "infer lit" (trace q1)
--   assertNonEmpty "infer lit" (eval q1)

--   -- Test 2: infer eempty cempty (ann (lam x.x) (int->int))
--   let q2 = query $ do
--         ty <- qfresh
--         env <- qfresh
--         pure (infer eempty cempty idAnn ty env, (ty, env))
--   printTrace "infer annotated id" (trace q2)
--   assertNonEmpty "infer annotated id" (eval q2)

--   -- Test 3: infer eempty cempty (app (ann (lam x.x) (int->int)) 1)
--   let q3 = query $ do
--         ty <- qfresh
--         env <- qfresh
--         pure (infer eempty cempty idApp ty env, (ty, env))
--   printTrace "infer annotated id app" (trace q3)
--   assertNonEmpty "infer annotated id app" (eval q3)

--   -- Test 4: infer eempty cempty (app (lam x.x) 1)
--   let q4 = query $ do
--         ty <- qfresh
--         env <- qfresh
--         pure (infer eempty cempty idAppUnann ty env, (ty, env))
--   printTrace "infer unannotated id app" (trace q4)
--   assertNonEmpty "infer unannotated id app" (eval q4)

--   -- Test 10: infer (ebound bot a top eempty) (ctype a) (lit 1)
--   let q10 = query $ do
--         ty <- qfresh
--         env <- qfresh
--         pure (infer (ebound tbot a0 ttop eempty) (ctype (tvar a0)) (lit one) ty env, (ty, env))
--   printTrace "infer bounded lit" (trace q10)
--   assertNonEmpty "infer bounded lit" (eval q10)

--   -- Test 11: sub (ebound bot a top eempty) int (ctype a)
--   let q11 = query $ do
--         env <- qfresh
--         ty <- qfresh
--         pure (sub (ebound tbot a0 ttop eempty) tint (ctype (tvar a0)) env ty, (env, ty))
--   printTrace "sub bounded int" (trace q11)
--   assertNonEmpty "sub bounded int" (eval q11)

--   -- Test 11 (ssub): ssub (ebound bot a top eempty) int <=- a
--   let q11s = query $ do
--         env <- qfresh
--         pure (ssub (ebound tbot a0 ttop eempty) tint neg (tvar a0) env, env)
--   printTrace "ssub bounded int" (trace q11s)
--   assertNonEmpty "ssub bounded int" (eval q11s)

--   -- Test 13: ssub eempty (int->int) <=+ (top->top) (expected fail)
--   let q13 = query $ do
--         env <- qfresh
--         pure (ssub eempty (tarr tint tint) pos (tarr ttop ttop) env, env)
--   printTrace "ssub expected fail" (trace q13)
--   assertEmpty "ssub expected fail" (eval q13)

  -- Test: id (g 1) and g (id 1) where g : forall b. int -> b, id : forall a. a -> a
  let gVar = nom 1
      idVar = nom 2
      b0 = tynom 1
      -- g : forall b. int -> b
      gTy = tforall b0 (tarr tint (tvar b0))
      -- id : forall a. a -> a
      idTy = tforall a0 (tarr (tvar a0) (tvar a0))
      -- environment with g and id
      envGId = etrm gVar gTy (etrm idVar idTy eempty)
      -- id (g 1)
      idGApp = app (var idVar) (app (var gVar) (lit one))

  -- let qPolyIdGTop = query $ do
  --       env <- qfresh
  --       pure (infer envGId (ctype ttop) idGApp ttop env, ttop)
  -- printTrace "infer id (g 1) : top (ctx top)" (trace qPolyIdGTop)
  -- assertNonEmpty "infer id (g 1) : top (ctx top)" (eval qPolyIdGTop)

  -- Test: envGId |- forall a. a -> a <: [g 1] ~> []
  -- let qSubForallIdG = query $ do
  --       env <- qfresh
  --       ty <- qfresh
  --       pure (sub envGId idTy (ctm (app (var gVar) (lit one)) cempty) env ty, (env, ty))
  -- printTrace "sub envGId (forall a. a -> a) <: [g 1] ~> []" (trace qSubForallIdG)
  -- assertNonEmpty "sub envGId (forall a. a -> a) <: [g 1] ~> []" (eval qSubForallIdG)

  -- Test: bot <: a <: top |- forall b. int -> b <: [1] -> a
  -- No
  let envBoundedA = ebound tbot a0 ttop eempty
  -- let qSubForallG = query $ do
  --       env <- qfresh
  --       ty <- qfresh
  --       pure (sub envBoundedA gTy (ctm (lit one) (ctype (tvar a0))) env ty, (env, ty))
  -- printTrace "sub (bot <: a <: top) (forall b. int -> b) <: [1] -> a" (trace qSubForallG)
  -- assertNonEmpty "sub (bot <: a <: top) (forall b. int -> b) <: [1] -> a" (eval qSubForallG)

  -- Test: bot <: a <: top |- forall b. int -> b <: [1] -> Int
  -- not work
  let qSubForallGInt = query $ do
        env <- qfresh
        ty <- qfresh
        pure (sub envBoundedA gTy (ctm (lit one) (ctype tint)) env ty, (env, ty))
  printTrace "sub (bot <: a <: top) (forall b. int -> b) <: [1] -> Int" (trace qSubForallGInt)
  assertNonEmpty "sub (bot <: a <: top) (forall b. int -> b) <: [1] -> Int" (eval qSubForallGInt)

  -- Test: forall a. a -> a <: [1] -> []
  -- works
  -- let qSubIdLit = query $ do
  --       env <- qfresh
  --       ty <- qfresh
  --       pure (sub eempty idTy (ctm (lit one) cempty) env ty, (env, ty))
  -- printTrace "sub (forall a. a -> a) <: [1] -> []" (trace qSubIdLit)
  -- assertNonEmpty "sub (forall a. a -> a) <: [1] -> []" (eval qSubIdLit)


  -- Test: bot <: a <: top, bot <: b <: top |- b <: a -| top <: a <: top, bot <: b <: top
  -- works
  let envBoundedAB = ebound tbot a0 ttop (ebound tbot b0 ttop eempty)
  -- let qSsubBA = query $ do
  --       env <- qfresh
  --       pure (ssub envBoundedAB (tvar b0) neg (tvar a0) env, env)
  -- printTrace "ssub (bot <: a <: top, bot <: b <: top) b <=- a" (trace qSsubBA)
  -- assertNonEmpty "ssub (bot <: a <: top, bot <: b <: top) b <=- a" (eval qSsubBA)

  -- Test: bot <: a <: top, bot <: b <: top |- b <:- int
  -- works
  -- let qSsubBInt = query $ do
  --       env <- qfresh
  --       pure (ssub envBoundedAB (tvar b0) neg tint env, env)
  -- printTrace "ssub (bot <: a <: top, bot <: b <: top) b <=- int" (trace qSsubBInt)
  -- assertNonEmpty "ssub (bot <: a <: top, bot <: b <: top) b <=- int" (eval qSsubBInt)

  -- Test: bot <: a <: top, bot <: b <: top |- int => 1 => ?
  -- works
  -- let qInferLitAB = query $ do
  --       ty <- qfresh
  --       env <- qfresh
  --       pure (infer envBoundedAB (ctype tint) (lit one) ty env, (ty, env))
  -- printTrace "infer (bot <: a <: top, bot <: b <: top) int => 1 => ?" (trace qInferLitAB)
  -- assertNonEmpty "infer (bot <: a <: top, bot <: b <: top) int => 1 => ?" (eval qInferLitAB)








  -- let qPolyGIdTop = query $ do
  --       env <- qfresh
  --       pure (infer envGId (ctype ttop) gIdApp ttop env, ttop)
  -- printTrace "infer g (id 1) : top (ctx top)" (trace qPolyGIdTop)
  -- assertNonEmpty "infer g (id 1) : top (ctx top)" (eval qPolyGIdTop)

  putStrLn ""
  putStrLn "=== Done ==="
