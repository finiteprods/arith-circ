{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards, DuplicateRecordFields, NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot, OverloadedLabels #-}
{-# LANGUAGE LambdaCase #-}
module Qap where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as M
import Data.IntMap.Merge.Strict qualified as MM
import Data.Foldable (fold)
import Data.Map qualified as Map
import Data.Array qualified as A
import Arithmetic (ArithCirc (unArithCirc), evalArithCirc, Wire(..), Gate(..))
import ZK.Algebra.API (ceilingLog2_, fromLog2, exp2_, Log2)
import ZK.Algebra.Pure.Poly (Poly, polyDiv, polyConst, vanishingPoly)
import ZK.Algebra.Pure.Field.Class (Field, PrimeField, FFTField, domainSubgroup)
import ZK.Algebra.Pure.NTT (intt)
import GHC.Generics (Generic)
import Optics.Core (over)
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (..))
import GHC.Stack (HasCallStack)
import Affine (affineCirc2Map)
import Prelude hiding (const)

-- | family of values in `a` consisting of a "constant"
-- and values "inputs", "intermediates", "outputs" indexed by integers
data Family a = Family
  { const :: a
  , ins   :: IntMap a
  , mids  :: IntMap a
  , outs  :: IntMap a
  } deriving (Show, Eq, Functor, Foldable, Generic)

-- | quadratic arithmetic program over field `f`
-- consisting of 3 families (*L*, *R*, *O*) of polynomials
-- and a vanishing polynomial *V*
data Qap f = Qap
  { insL   :: Family (Poly f)
  , insR   :: Family (Poly f)
  , outs   :: Family (Poly f)
  , vanish :: Poly f
  } deriving (Show, Eq)

-- | like `Qap` but with `Poly` generalised to an arbitrary functor `p`
data GenQap p f = GenQap
  { insL   :: Family (p f)
  , insR   :: Family (p f)
  , outs   :: Family (p f)
  , vanish :: p f
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
  { const = f xs.const ys.const
  , ins  = mergeMaps xs.ins  ys.ins
  , mids = mergeMaps xs.mids ys.mids
  , outs = mergeMaps xs.outs ys.outs
  }
  where
    mergeMaps = MM.merge onMissingKey2 onMissingKey1 onMatchKey
    onMissingKey2 = MM.mapMissing $ \_ x -> f x y0
    onMissingKey1 = MM.mapMissing $ \_ y -> f x0 y
    onMatchKey    = MM.zipWithMatched $ \_ x y -> f x y

-- | @mergeFamilies' f y0 xs ys@ merges `xs` and `ys` with a given function `f` on values
-- s.t. `(k, x)` merged with `(k, y)` is `(k, f x y)`
-- but if `k` isn't a key in `ys` then it's `(k, f x y0)`
-- and if `k` isn't a key in `xs` then it's `(k, y)`
mergeFamilies'
  :: (a -> b -> b)
  -> b
  -> Family a
  -> Family b
  -> Family b
mergeFamilies' f y0 xs ys = Family
  { const = f xs.const ys.const
  , ins   = mergeMaps xs.ins  ys.ins
  , mids  = mergeMaps xs.mids ys.mids
  , outs  = mergeMaps xs.outs ys.outs
  } where
    mergeMaps = MM.merge onMissingKey2 MM.preserveMissing onMatchKey
    onMissingKey2 = MM.mapMissing     $ \_ x   -> f x y0
    onMatchKey    = MM.zipWithMatched $ \_ x y -> f x y

-- | `intersectionWith` on `Map`s lifted to `Family`s
intersectionWith
  :: (a -> b -> c)
  -> Family a
  -> Family b
  -> Family c
intersectionWith f xs ys = Family
  { const = f xs.const ys.const
  , ins  = intersection xs.ins  ys.ins
  , mids = intersection xs.mids ys.mids
  , outs = intersection xs.outs ys.outs
  }
  where
    intersection = M.intersectionWith f

-- | transposes a list of families into a family of lists
sequenceFamily :: Num a => [Family a] -> Family [a]
sequenceFamily = foldr (mergeFamilies (:) 0 []) (constFamily [])

-- | witness the given assignment *c* of variables as valid for the given QAP
-- i.e. "plugging" *c* into the QAP satisfies "inL * inR = out" for all mult gates
-- i.e. the polynomial *LR - O* vanishes for all mult gates specified by *V*
-- more precisely, *LR - O = QV* for some quotient polynomial *Q*
-- in which case, *Q* (witnessing divisibility by *V*) is returned
witness :: (Eq f, Field f)
  => Qap f    -- ^ circuit in QAP form
  -> Family f -- ^ assignment of input, output and intermediate values
  -> Maybe (Poly f)
witness = witnessZk 0 0 0

-- | `witness` in zero knowledge
witnessZk :: (Eq f, Field f)
  => f -- ^ randomness to *L*
  -> f -- ^ randomness to *R*
  -> f -- ^ randomness to *O*
  -> Qap f
  -> Family f
  -> Maybe (Poly f)
witnessZk d1 d2 d3 Qap{..} trace =
  if r == 0 then Just q else Nothing
  where
    (q, r) = masterPoly `polyDiv` vanish
    masterPoly = inlPoly * inrPoly - outPoly
    inlPoly = sumPolys (scaleByTrace insL) + vanish * polyConst d1
    inrPoly = sumPolys (scaleByTrace insR) + vanish * polyConst d2
    outPoly = sumPolys (scaleByTrace outs) + vanish * polyConst d3
    scaleByTrace = intersectionWith ((*) . polyConst) trace
    sumPolys = foldFamily (+)

-- | generate a valid assignment of variables (aka trace) for the given circuit
assignment :: PrimeField f
  => ArithCirc f
  -> IntMap f -- ^ inputs to the circuit
  -> Family f
assignment circ = evalArithCirc (flip lookupWire) updateWire circ . insFamily

-- | lookup value of wire in given family
lookupWire :: Family a -> Wire -> Maybe a
lookupWire Family{..} = \case
  Input lbl        -> M.lookup lbl ins
  Intermediate lbl -> M.lookup lbl mids
  Output lbl       -> M.lookup lbl outs

-- | update value of wire in given family
updateWire :: Wire -> a -> Family a -> Family a
updateWire = \case
  Input lbl        -> over #ins  . M.insert lbl
  Intermediate lbl -> over #mids . M.insert lbl
  Output lbl       -> over #outs . M.insert lbl
--  \v fam -> over #outs (M.insert lbl v) fam

-- | convert gate into a "mini-QAP"
gate2GenQap :: (Field f, HasCallStack) => Gate Wire f -> GenQap Identity f
gate2GenQap Mul{..} = GenQap
  { insL = Map.foldrWithKey updateWire (constFamily constL) mapL <&> Identity
  , insR = Map.foldrWithKey updateWire (constFamily constR) mapR <&> Identity
  , outs = updateWire mulO 1 (constFamily 0)
  , vanish = 0
  } where
    (constL, mapL) = affineCirc2Map mulL
    (constR, mapR) = affineCirc2Map mulR

gate2GenQap _ = error "not yet implemented for non-multiplication gates"

-- | transpose a list of "point-based QAPs" into a single list-based one
sequenceGenQap :: Num f => [GenQap Identity f] -> GenQap [] f
sequenceGenQap gqaps = GenQap
  { insL = sequenceFamily $ fmap runIdentity . (.insL) <$> gqaps
  , insR = sequenceFamily $ fmap runIdentity . (.insR) <$> gqaps
  , outs = sequenceFamily $ fmap runIdentity . (.outs) <$> gqaps
  , vanish = runIdentity . (.vanish) <$> gqaps
  }

-- | interpolate (via FFT, specifically iNTT) points-based QAP into a polynomials-based QAP
interpolatePolys :: FFTField f => GenQap [] f -> Qap f
interpolatePolys GenQap{..} = Qap
  { insL = interpolate . toArray . pad0s <$> insL
  , insR = interpolate . toArray . pad0s <$> insR
  , outs = interpolate . toArray . pad0s <$> outs
  , vanish = vanishingPoly . domainSubgroup $ fromLog2 nextPowOf2
  } where
    nextPowOf2 = ceilingLog2_ (length vanish)
    pad0s ys = ys ++ replicate (exp2_ nextPowOf2 - length ys) 0
    toArray = A.listArray (0, exp2_ nextPowOf2 - 1)
    interpolate = intt . domainSubgroup $ fromLog2 nextPowOf2

-- | pad list with zeros until length is a power of two
padToPowOf2 :: Num f => [f] -> ([f], Log2)
padToPowOf2 ys = (ys ++ replicate padLen 0, nextPow)
  where
    len = length ys
    nextPow = ceilingLog2_ len
    padLen = exp2_ nextPow - len

-- | convert arithmetic circuit to QAP
arithCirc2Qap ::FFTField f => ArithCirc f -> Qap f
arithCirc2Qap = interpolatePolys . arithCirc2GenQap

arithCirc2GenQap :: Field f => ArithCirc f -> GenQap [] f
arithCirc2GenQap = sequenceGenQap . map gate2GenQap . unArithCirc
