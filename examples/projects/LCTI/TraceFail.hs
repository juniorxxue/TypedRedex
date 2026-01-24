module LCTI.TraceFail (main) where

import Control.Exception (evaluate)
import System.Timeout (timeout)

import TypedRedex.Backend.Eval (query, qfresh)
import TypedRedex.Core.Term (ground)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivationWithOmit, trace)

import LCTI.Main (Expectation(..), TestCase(..), preEnv, testCases)
import LCTI.Rules (infer)
import LCTI.Syntax (cempty)

data CaseStatus
  = CaseOk
  | CaseUnexpectedPass
  | CaseNoTrace
  | CaseTimeout
  deriving (Eq, Show)

timeoutMicros :: Int
timeoutMicros = 5 * 1000000

omitTraceNames :: [String]
omitTraceNames =
  [ "skip-trm"
  , "skip-uvar"
  , "skip-evar"
  , "skip-svar"
  ]

main :: IO ()
main = do
  putStrLn "=== LCTI Trace (expected failures) ==="
  let failCases = filter isExpectFail testCases
  results <- mapM (runCase timeoutMicros) failCases
  let paired = zip failCases results
      count status = length [() | (_, s) <- paired, s == status]
      timeouts = [tcName tc | (tc, s) <- paired, s == CaseTimeout]
      unexpected = [tcName tc | (tc, s) <- paired, s == CaseUnexpectedPass]
      noTrace = [tcName tc | (tc, s) <- paired, s == CaseNoTrace]
  putStrLn "=== Summary ==="
  putStrLn ("Total: " ++ show (length failCases))
  putStrLn ("TraceFail: " ++ show (count CaseOk))
  putStrLn ("Unexpected pass: " ++ show (count CaseUnexpectedPass))
  putStrLn ("No trace result: " ++ show (count CaseNoTrace))
  putStrLn ("Timeouts: " ++ show (count CaseTimeout))
  reportList "Unexpected pass cases" unexpected
  reportList "No trace result cases" noTrace
  reportList "Timed out cases" timeouts

reportList :: String -> [String] -> IO ()
reportList label names =
  case names of
    [] -> pure ()
    _ -> putStrLn (label ++ ": " ++ show names)

isExpectFail :: TestCase -> Bool
isExpectFail tc =
  case tcExpect tc of
    ExpectFail -> True
    _ -> False

runCase :: Int -> TestCase -> IO CaseStatus
runCase micros tc = do
  putStrLn ("-- " ++ tcName tc)
  outcome <- timeout micros $ do
    let q = query $ do
          ty <- qfresh
          pure (infer (ground preEnv) cempty (ground (tcTerm tc)) ty, ty)
    results <- evaluate (trace q)
    case results of
      TraceFail _ deriv : _ -> do
        putStrLn (prettyDerivationWithOmit omitTraceNames deriv)
        pure CaseOk
      TraceOk _ _ : _ -> do
        putStrLn "[UNEXPECTED PASS]"
        pure CaseUnexpectedPass
      [] -> do
        putStrLn "[NO TRACE RESULT]"
        pure CaseNoTrace
  case outcome of
    Nothing -> do
      putStrLn "[TIMEOUT]"
      pure CaseTimeout
    Just status -> pure status
