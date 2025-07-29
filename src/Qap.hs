{-# LANGUAGE StrictData, RecordWildCards #-}

module Qap where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as M
import Data.IntMap.Merge.Strict qualified as MM
import Data.Foldable (fold)
import Data.Poly (VPoly, scale, quotRemFractional)

-- | family of values `p` grouped by constant, inputs, intermediates, outputs.
data Family p = Family
  { famConst :: p
  , famIns  :: IntMap p
  , famMids :: IntMap p
  , famOuts :: IntMap p
  } deriving (Show, Eq, Functor, Foldable)

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
constFamily :: p -> Family p
constFamily x = Family
  { famConst = x
  , famIns  = M.empty
  , famMids = M.empty
  , famOuts = M.empty
  }

-- | create `Family` with given constant and inputs
constInsFamily :: p -> IntMap p -> Family p
constInsFamily x ins = Family
  { famConst = x
  , famIns  = ins
  , famMids = M.empty
  , famOuts = M.empty
  }

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
  { famConst = famConst xs `f` famConst ys
  , famIns  = famIns  xs `mergeMaps` famIns  ys
  , famMids = famMids xs `mergeMaps` famMids ys
  , famOuts = famOuts xs `mergeMaps` famOuts ys
  }
  where
    mergeMaps = MM.merge onMissingKey2 onMissingKey1 onMatchKey
    onMissingKey2 = MM.mapMissing $ \_ x -> f x y0
    onMissingKey1 = MM.mapMissing $ \_ y -> f x0 y
    onMatchKey    = MM.zipWithMatched $ \_ x y -> f x y

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
    scaleByTrace = mergeFamilies (scale 0) 0 0 trace
    sumPolys = foldFamily (+)
