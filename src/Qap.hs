{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards, NoFieldSelectors, OverloadedRecordDot #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE LambdaCase #-}
module Qap where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as M
import Data.IntMap.Merge.Strict qualified as MM
import Data.Foldable (fold)
import Data.Poly (VPoly, scale, quotRemFractional)
import Arithmetic (ArithCirc, evalArithCirc, Wire(..))
import ZK.Algebra.API (PrimeField)
import GHC.Generics (Generic)
import Optics.Core (over)

-- | family of values `a` grouped by constant, inputs, intermediates, outputs.
data Family a = Family
  { famConst :: a
  , famIns  :: IntMap a
  , famMids :: IntMap a
  , famOuts :: IntMap a
  } deriving (Show, Eq, Functor, Foldable, Generic)

-- | quadratic arithmetic program over field `f`
-- consisting of 3 families (L, R, O) of polynomials
-- and a vanishing polynomial V
data Qap f = Qap
  { qapInsL :: Family (VPoly f)
  , qapInsR :: Family (VPoly f)
  , qapOuts :: Family (VPoly f)
  , qapVanish :: VPoly f
  } deriving (Show, Eq)

-- | like `Qap` but `Poly` generalised to an arbitrary functor `p`
data GenQap p f = GenQap
  { genQapInsL :: Family (p f)
  , genQapInsR :: Family (p f)
  , genQapOuts :: Family (p f)
  , genQapVanish :: p f
  } deriving (Show, Eq, Functor)

-- | create `Family` with given constant
constFamily :: a -> Family a
constFamily x = Family x M.empty M.empty M.empty

-- | create `Family` with given constant and inputs
constInsFamily :: a -> IntMap a -> Family a
constInsFamily x ins = Family x ins M.empty M.empty

-- | create `Family` with given inputs
insFamily :: Num a => IntMap a -> Family a
insFamily ins = Family 1 ins M.empty M.empty

sumFamily, sumFamilyConstIns, sumFamilyMidsOuts :: Monoid p => Family p -> p
-- | add all values in a `Family`
sumFamily = fold
-- | add constant and all inputs
sumFamilyConstIns (Family konst ins _ _) = konst <> fold ins
-- | add all intermediates and outputs
sumFamilyMidsOuts (Family _ _ mids outs) = fold mids <> fold outs

-- | fold with binary operation assumed to be commutative
foldFamily :: (p -> p -> p) -> Family p -> p
foldFamily = foldr1

-- | `mergeFamilies f x0 y0 xs ys` merges `xs` and `ys` with a given function `f` on values
-- s.t. `(k, x)` merged with `(k, y)` is `(k, f x y)`
-- but if `k` isn't a key in `ys` then it's `(k, f x y0)`
-- otoh if `k` isn't a key in `xs` then it's `(k, f x0 y)`
mergeFamilies
  :: (a -> b -> c) -- ^ function on values
  -> a -- ^ default value to use in function when key in 2nd family is missing in 1st
  -> b -- ^ default value to use in function when key in 1st family is missing in 2nd
  -> Family a -- ^ first family
  -> Family b -- ^ second family
  -> Family c
mergeFamilies f x0 y0 xs ys = Family
  { famConst = f xs.famConst ys.famConst
  , famIns  = mergeMaps xs.famIns  ys.famIns
  , famMids = mergeMaps xs.famMids ys.famMids
  , famOuts = mergeMaps xs.famOuts ys.famOuts
  }
  where
    mergeMaps = MM.merge onMissingKey2 onMissingKey1 onMatchKey
    onMissingKey2 = MM.mapMissing $ \_ x -> f x y0
    onMissingKey1 = MM.mapMissing $ \_ y -> f x0 y
    onMatchKey    = MM.zipWithMatched $ \_ x y -> f x y

-- | `intersectionWith` on maps lifted to `Family`s
intersectionWith
  :: (a -> b -> c)
  -> Family a
  -> Family b
  -> Family c
intersectionWith f xs ys = Family
  { famConst = f xs.famConst ys.famConst
  , famIns  = intersection xs.famIns  ys.famIns
  , famMids = intersection xs.famMids ys.famMids
  , famOuts = intersection xs.famOuts ys.famOuts
  }
  where
    intersection = M.intersectionWith f

-- | witness the given assignment c of variables as valid for the given QAP
-- i.e. "plugging" c into the QAP satisfies "inL * inR = out" for all all mult gates
-- i.e. the polynomial LR - O vanishes for all mult gates specified by V
-- more precisely, LR - O = QV for some quotient polynomial Q
-- in which case, Q (witnessing divisibility by V) is returned
witness :: (Eq f, Fractional f)
  => Qap f    -- ^ circuit in QAP form
  -> Family f -- ^ assignment of input, output and intermediate values
  -> Maybe (VPoly f)
witness = witnessZk 0 0 0

-- | `witness` in zero knowledge
witnessZk :: (Eq f, Fractional f)
  => f -- ^ randomness to L
  -> f -- ^ randomness to R
  -> f -- ^ randomness to O
  -> Qap f
  -> Family f
  -> Maybe (VPoly f)
witnessZk d1 d2 d3 Qap {..} trace =
  if r == 0 then Just q else Nothing
  where
    (q, r) = quotRemFractional masterPoly qapVanish
    masterPoly = inlPoly * inrPoly - outPoly
    inlPoly = sumPolys (scaleByTrace qapInsL) + scale 0 d1 qapVanish
    inrPoly = sumPolys (scaleByTrace qapInsR) + scale 0 d2 qapVanish
    outPoly = sumPolys (scaleByTrace qapOuts) + scale 0 d3 qapVanish
    scaleByTrace = intersectionWith (scale 0) trace
    sumPolys = foldFamily (+)

-- | generate a valid assignment of variables (aka trace) for the given circuit
assignment :: PrimeField f
  => ArithCirc f
  -> IntMap f -- ^ inputs to the circuit
  -> Family f
assignment circ = evalArithCirc (flip lookupWire) updateWire circ . insFamily

-- | lookup value of wire in given family
lookupWire :: Family a -> Wire -> Maybe a
lookupWire Family {..} = \case
  Input lbl        -> M.lookup lbl famIns
  Intermediate lbl -> M.lookup lbl famMids
  Output lbl       -> M.lookup lbl famOuts

-- | update value of wire in given family
updateWire :: Wire -> a -> Family a -> Family a
updateWire = \case
  Input lbl        -> over #famIns  . M.insert lbl
  Intermediate lbl -> over #famMids . M.insert lbl
  Output lbl       -> over #famOuts . M.insert lbl
