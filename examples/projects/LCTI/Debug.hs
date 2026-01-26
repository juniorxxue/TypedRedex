module LCTI.Debug (main) where

import Control.Exception (evaluate)
import Control.Monad (forM_, when)
import qualified Data.Set as S
import System.Environment (getArgs)
import System.Timeout (timeout)
import Text.Read (readMaybe)

import TypedRedex.Backend.Eval (query, qfresh)
import TypedRedex.Core.Term (ground)
import TypedRedex.Interp.Debug (DebugOpts(..), DebugResult(..), debugWith, defaultDebugOpts)
import TypedRedex.Interp.Trace (Failure(..))

import LCTI.Main (Expectation(..), TestCase(..), preEnv, testCases)
import LCTI.Rules (infer)
import LCTI.Syntax (cempty)

-- Keep output focused on "interesting" rules (same idea as TraceFail.hs).
omitNames :: [String]
omitNames =
  [ "skip-trm"
  , "skip-uvar"
  , "skip-evar"
  , "skip-svar"
  ]

-- | Base timeout (5 seconds). Extended when delay is used.
baseTimeoutMicros :: Int
baseTimeoutMicros = 5 * 1000000

-- | Calculate timeout based on delay setting.
-- If delay is used, extend timeout significantly (or disable with 0 delay factor).
calcTimeout :: Int -> Int
calcTimeout delayMicros
  | delayMicros > 0 = baseTimeoutMicros + delayMicros * 1000  -- Add ~1000 lines worth of delay
  | otherwise = baseTimeoutMicros

-- | Parse command line arguments for delay (in milliseconds).
parseDelay :: [String] -> Int
parseDelay [] = 0
parseDelay ("--delay":ms:rest) = maybe (parseDelay rest) (* 1000) (readMaybe ms)
parseDelay ("-d":ms:rest) = maybe (parseDelay rest) (* 1000) (readMaybe ms)
parseDelay (_:rest) = parseDelay rest

-- | Parse command line arguments for specific test cases to run.
parseTestIndices :: [String] -> Maybe [Int]
parseTestIndices [] = Nothing
parseTestIndices ("--tests":idxStr:_) = Just $ map read $ words $ map (\c -> if c == ',' then ' ' else c) idxStr
parseTestIndices ("-t":idxStr:_) = Just $ map read $ words $ map (\c -> if c == ',' then ' ' else c) idxStr
parseTestIndices (_:rest) = parseTestIndices rest

-- | Check if --no-animate flag is present
parseNoAnimate :: [String] -> Bool
parseNoAnimate = elem "--no-animate"

-- | Check if --no-color flag is present
parseNoColor :: [String] -> Bool
parseNoColor = elem "--no-color"

-- | Check if --no-timeout flag is present
parseNoTimeout :: [String] -> Bool
parseNoTimeout = elem "--no-timeout"

main :: IO ()
main = do
  args <- getArgs
  let delay = parseDelay args
      maybeIndices = parseTestIndices args
      noAnimate = parseNoAnimate args
      noColor = parseNoColor args
      noTimeout = parseNoTimeout args

  putStrLn "=== LCTI Debug Interpreter ==="
  putStrLn ""
  putStrLn "Usage: example-lcti-debug [options]"
  putStrLn "  --delay|-d <ms>  : Add delay between output lines (for step-by-step viewing)"
  putStrLn "  --tests|-t <n,n> : Run specific test indices (comma-separated)"
  putStrLn "  --no-animate     : Disable animation (show all rule attempts)"
  putStrLn "  --no-color       : Disable colored output"
  putStrLn "  --no-timeout     : Disable timeout (for slow step-by-step viewing)"
  putStrLn ""
  when (delay > 0) $
    putStrLn $ "Delay: " ++ show (delay `div` 1000) ++ "ms per line"
  when noAnimate $
    putStrLn "Animation: disabled"
  when noColor $
    putStrLn "Colors: disabled"
  when noTimeout $
    putStrLn "Timeout: disabled"
  putStrLn ""

  -- Select test cases to run
  let failingCases = filter isExpectFail testCases
      selectedCases = case maybeIndices of
        Just indices -> [failingCases !! i | i <- indices, i >= 0, i < length failingCases]
        Nothing -> take 30 failingCases  -- Default: first 30 failing cases

  -- Show which tests we're running
  putStrLn $ "Running " ++ show (length selectedCases) ++ " test case(s):"
  forM_ (zip [(0::Int)..] selectedCases) $ \(i, tc) ->
    putStrLn $ "  [" ++ show i ++ "] " ++ tcName tc
  putStrLn ""

  -- Run each test case
  forM_ (zip [(1::Int)..] selectedCases) $ \(i, tc) -> do
    putStrLn $ replicate 60 '='
    putStrLn $ "Test " ++ show i ++ "/" ++ show (length selectedCases) ++ ": " ++ tcName tc
    putStrLn $ replicate 60 '='
    runCase delay (not noAnimate) (not noColor) noTimeout tc
    putStrLn ""

isExpectFail :: TestCase -> Bool
isExpectFail tc =
  case tcExpect tc of
    ExpectFail -> True
    _ -> False

runCase :: Int -> Bool -> Bool -> Bool -> TestCase -> IO ()
runCase delay animate colors noTimeout tc = do
  let q = query $ do
        ty <- qfresh
        pure (infer (ground preEnv) cempty (ground (tcTerm tc)) ty, ty)
      opts =
        defaultDebugOpts
          { dbgShowConstraints = False
          , dbgOmitNames = S.fromList omitNames
          , dbgDelayMicros = delay
          , dbgVerbose = True
          , dbgAnimate = animate
          , dbgColors = colors
          }
      runDebug = evaluate =<< debugWith opts q
  outcome <- if noTimeout
    then Just <$> runDebug
    else timeout (calcTimeout delay) runDebug
  putStrLn ""
  putStrLn $ replicate 40 '-'
  case outcome of
    Nothing -> putStrLn "Result: TIMEOUT"
    Just results ->
      case results of
        DebugOk ty : _ -> do
          putStrLn "[UNEXPECTED PASS]"
          putStrLn $ "  Type: " ++ show ty
        DebugFail failure : _ -> do
          putStrLn $ "Result: FAIL (expected)"
          putStrLn $ "  Reason: " ++ failureDescription failure
        [] -> putStrLn "Result: NO RESULT"

failureDescription :: Failure -> String
failureDescription (FailMode msg) = "mode error: " ++ takeWhile (/= '\n') msg
failureDescription (FailHead msg) = "no matching rule: " ++ takeWhile (/= '\n') msg
failureDescription (FailPremise msg) = "premise failed: " ++ takeWhile (/= '\n') msg
failureDescription (FailConstraint msg) = "constraint failed: " ++ takeWhile (/= '\n') msg
failureDescription (FailNegation msg) = "negation failed: " ++ msg
