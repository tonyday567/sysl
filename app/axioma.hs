-- | SysL oracle suite: polynomial encoding and @These@ boundaries.
module Main where

import Circuit.Layer (run)
import Circuit.Process (scan)
import Data.These (These (..))
import SysL

main :: IO ()
main = do
  putStrLn "sysl-axioma oracles"
  let results =
        [ s1OneRoundTrip,
          s2TimesRoundTrip,
          s3PlusRoundTrip,
          s4HomBetaEta,
          s5ThenRoundTrip,
          s6GradedHomDispatch,
          s7MuIdentity,
          s8ComuCorecursion,
          s9DirectAgreesWithLoop,
          s10DirectAgreesWithProcess
        ]
  if and results
    then putStrLn "all green"
    else do
      putStrLn "failures detected"
      mapM_ (putStrLn . show) (zip [(1 :: Int) ..] results)

-- ---------------------------------------------------------------------------
-- Oracle helpers
-- ---------------------------------------------------------------------------

assertEq :: (Eq a, Show a) => String -> a -> a -> Bool
assertEq name expected actual =
  if expected == actual
    then True
    else
      error $
        name
          <> ": expected "
          <> show expected
          <> ", got "
          <> show actual

getInt :: Val Int -> Int
getInt (VEmbed n) = n
getInt _ = error "getInt: expected VEmbed"

-- ---------------------------------------------------------------------------
-- S1: One unit laws
-- ---------------------------------------------------------------------------

s1OneRoundTrip :: Bool
s1OneRoundTrip =
  let v = VUnit :: Val ()
      ev = valToEval @'One v
      v' = evalToVal @'One ev
   in assertEq "S1 One round-trip" v v'

-- ---------------------------------------------------------------------------
-- S2: Times associativity / symmetry
-- ---------------------------------------------------------------------------

s2TimesRoundTrip :: Bool
s2TimesRoundTrip =
  let v = VPair VUnit (VPair VUnit VUnit) :: Val ()
      ev = valToEval @('Times 'One ('Times 'One 'One)) v
      v' = evalToVal @('Times 'One ('Times 'One 'One)) ev
   in assertEq "S2 Times round-trip" v v'

-- ---------------------------------------------------------------------------
-- S3: Plus left / right injections and pattern matching
-- ---------------------------------------------------------------------------

s3PlusRoundTrip :: Bool
s3PlusRoundTrip =
  let leftV = VLeft VUnit :: Val ()
      rightV = VRight VUnit :: Val ()
      leftE = valToEval @('Plus 'One 'One) leftV
      rightE = valToEval @('Plus 'One 'One) rightV
      leftV' = evalToVal @('Plus 'One 'One) leftE
      rightV' = evalToVal @('Plus 'One 'One) rightE
   in assertEq "S3 Plus left" leftV leftV'
      && assertEq "S3 Plus right" rightV rightV'

-- ---------------------------------------------------------------------------
-- S4: Hom beta/eta
-- ---------------------------------------------------------------------------

s4HomBetaEta :: Bool
s4HomBetaEta =
  let -- identity function applied to VUnit
      cmd =
        Cut
          (Embed (HomComatch (Cut (Embed (Var 0)) (Covar 0))))
          (HomCointro (Embed (Var 0)) (Covar 0))
      direct = evalCommand cmd [VUnit]
      looped = run (commandToLoop cmd) [VUnit]
   in assertEq "S4 Hom direct" (That (0, VUnit) :: Result ()) direct
      && assertEq "S4 Hom loop" (That (0, VUnit) :: Result ()) looped

-- ---------------------------------------------------------------------------
-- S5: Then forward/backward round-trip
-- ---------------------------------------------------------------------------

s5ThenRoundTrip :: Bool
s5ThenRoundTrip =
  let -- lens: forward doubles, backward halves
      l = thenLens (\x -> VEmbed (getInt x * 2)) (\_ y -> VEmbed (getInt y `div` 2))
      (fwd, bw) = applyThen l (VEmbed 6)
      back = bw fwd
   in assertEq "S5 Then forward" (VEmbed 12) fwd
      && assertEq "S5 Then backward" (VEmbed 6) back

-- ---------------------------------------------------------------------------
-- S6: GradedHom slot dispatch
-- ---------------------------------------------------------------------------

s6GradedHomDispatch :: Bool
s6GradedHomDispatch =
  let -- graded function: even -> slot 0, odd -> slot 1
      gf =
        VGradedFun $ \x ->
          let n = getInt x
           in if even n then That (0, VEmbed (n + 1)) else That (1, VEmbed (n - 1))
      -- coterm dispatch: slot 0 returns unit, slot 1 returns unit
      coterm = GradedHomCointro (Embed (Var 0)) [Covar 0, Covar 1]
      cmdEven = Cut (Embed (Lit gf)) coterm
      cmdOdd = Cut (Embed (Lit gf)) coterm
      resEven = evalCommand cmdEven [VEmbed 4]
      resOdd = evalCommand cmdOdd [VEmbed 5]
   in assertEq "S6 GradedHom even slot" (That (0, VEmbed 5) :: Result Int) resEven
      && assertEq "S6 GradedHom odd slot" (This (1, VEmbed 4) :: Result Int) resOdd

-- ---------------------------------------------------------------------------
-- S7: Mu fixed-point identity via trace
-- ---------------------------------------------------------------------------

s7MuIdentity :: Bool
s7MuIdentity =
  let -- Mu of the identity command returns the focus value.
      term = Mu (Cut (Embed (Var 0)) (Covar 0))
      direct = evalTerm term [VUnit]
      looped = run (termToLoop term) [VUnit]
   in assertEq "S7 Mu direct" (That VUnit :: These (Output ()) (Val ())) direct
      && assertEq "S7 Mu loop" (That VUnit :: These (Output ()) (Val ())) looped

-- ---------------------------------------------------------------------------
-- S8: Comu corecursion
-- ---------------------------------------------------------------------------

s8ComuCorecursion :: Bool
s8ComuCorecursion =
  let -- Comu prepends the focus value to the environment and runs the command.
      coterm = Comu (Cut (Embed (Var 0)) (Covar 0))
      cmd = Cut (Embed (Lit (VEmbed 7 :: Val Int))) coterm
      direct = evalCommand cmd []
      looped = run (commandToLoop cmd) []
   in assertEq "S8 Comu direct" (That (0, VEmbed 7) :: Result Int) direct
      && assertEq "S8 Comu loop" (That (0, VEmbed 7) :: Result Int) looped

-- ---------------------------------------------------------------------------
-- S9: Direct evaluator agrees with Loop interpreter
-- ---------------------------------------------------------------------------

s9DirectAgreesWithLoop :: Bool
s9DirectAgreesWithLoop =
  assertEq "S9 testId" testId testIdLoop
    && assertEq "S9 testThen" testThen testThenLoop

-- ---------------------------------------------------------------------------
-- S10: Direct evaluator agrees with Process interpreter
-- ---------------------------------------------------------------------------

s10DirectAgreesWithProcess :: Bool
s10DirectAgreesWithProcess =
  let term = Embed (Lit VUnit)
      direct = evalTerm term []
      processValue = case scan (evalProcess term) [[]] of
        [v] -> v
        _ -> error "S10: process produced unexpected output count"
   in case direct of
        That VUnit ->
          assertEq "S10 Process agrees" (VUnit :: Val ()) processValue
        _ -> error "S10: direct term did not return VUnit"
