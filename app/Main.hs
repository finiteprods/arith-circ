{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

import Arithmetic (ArithCirc, Wire)
import Expr (runCircBuilder)
import Lang (mul, var, input, compile2Out)
import Qap (Qap, arithCirc2Qap, Family, assignment, witness)
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

trace :: Family Fr
trace = assignment (snd circ) ins
  where
    ins = M.fromList $ zip [0..] [6, 8]

main :: IO ()
main = do
  case witness qap trace of
    Nothing -> putStrLn "invalid trace"
    Just w  -> print w
