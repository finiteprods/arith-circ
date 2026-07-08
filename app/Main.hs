{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

import Affine
import Arithmetic
import Expr
import Lang (mul, var, input, compile2Out)
import Qap
import Data.IntMap.Strict qualified as M
import ZK.Algebra.Pure.Instances.BN254 (Fr)
import ZK.Algebra.Pure.Field (FFTField (..))

-- (orphan) instance as zk library does not provide it
instance FFTField Fr where
  domainGenPxy _ =
    19103219067921713944291392827692070036145651957329286315305642004821462161904
  domainLogSize _ = 28

circ :: (Wire, ArithCirc Fr)
circ = runCircBuilder $ do
  i0 <- var <$> input
  i1 <- var <$> input
  let m2 = mul i0 i1
  compile2Out m2

qap :: Qap Fr
qap = arithCirc2Qap (snd circ)

qap' :: Qap Fr
qap' = arithCirc2Qap circ2

trace :: Family Fr
trace = assignment (snd circ) ins
  where
    ins = M.fromList $ zip [0..] [6, 8]

trace' :: Family Fr
trace' = assignment circ2 ins
  where
    ins = M.fromList $ zip [0..] [2, 3, 4, 5]

main :: IO ()
main = do
  case witness qap' trace' of
    Nothing -> putStrLn "invalid trace"
    Just w  -> print w

circ2 :: ArithCirc Fr
circ2 = ArithCirc
  [ Mul (Var (Input 0)) (Var (Input 1)) (Intermediate 0)
  , Mul (Var (Input 2)) (Var (Input 3)) (Intermediate 1)
  , Mul (Add (ConstGate 10) (Var (Intermediate 0))) (Var (Intermediate 1)) (Output 0)
  ]

circYupeng :: ArithCirc Fr
circYupeng = ArithCirc
  [ Mul (Var (Input 1)) (Var (Input 2)) (Intermediate 7)
  , Mul (Var (Intermediate 7)) (Add (Var (Input 3)) (Var (Input 4))) (Output 8)
  , Mul (Add (Var (Input 3)) (Var (Input 4))) (Add (Var (Input 5)) (Var (Input 6))) (Output 9)
  ]

traceYupeng :: Family Fr
traceYupeng = assignment circYupeng ins
  where
    ins = M.fromList $ zip [1..] [3, 2, 1, 7, 5, 4]
