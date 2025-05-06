{-# LANGUAGE LambdaCase, StrictData #-}

--  | Definition of arithmetic circuits that only contain addition, scalar
--  multiplication and constant gates along with its direct evaluation and
--  translation into affine maps.
module Affine where

import GHC.Stack (HasCallStack)
import Data.Map (Map)
import qualified Data.Map as Map

-- | Arithmetic circuits without multiplication
-- i.e. circuits describe affine transformations.
data AffineCirc i f
  = Add (AffineCirc i f) (AffineCirc i f)
  | ScalarMul f (AffineCirc i f)
  | ConstGate f
  | Var i
  deriving (Read, Eq, Show)

collectInputsAffine :: AffineCirc i f -> [i]
collectInputsAffine = \case
  Add c1 c2     -> collectInputsAffine c1 ++ collectInputsAffine c2
  ScalarMul _ c -> collectInputsAffine c
  ConstGate _   -> []
  Var x         -> [x]

-- | Rename variables.
mapVarsAffine :: (i -> j) -> AffineCirc i f -> AffineCirc j f
mapVarsAffine f = \case
  Add c1 c2     -> Add (mapVarsAffine f c1) (mapVarsAffine f c2)
  ScalarMul s c -> ScalarMul s (mapVarsAffine f c)
  ConstGate k   -> ConstGate k
  Var x         -> Var (f x)

-- | Evaluate affine circuit on the given environment.
evalAffineCirc :: (Num f, HasCallStack)
  -- | Lookup logic
  => (i -> vars -> Maybe f)
  -- | Environment
  -> vars
  -> AffineCirc i f
  -> f

evalAffineCirc lkp env = \case
  Add c1 c2     -> evalAffineCirc lkp env c1 + evalAffineCirc lkp env c2
  ScalarMul s c -> s * evalAffineCirc lkp env c
  ConstGate k   -> k
  Var x         -> case lkp x env of
    Just v  -> v
    Nothing -> error "incorrect variable lookup"

-- | Convert affine circuit to a vector representing the evaluation function
-- using a @Map@ to represent the potentially sparse vector.
affineCirc2Map :: (Num f, Ord i)
  => AffineCirc i f
  -- | Constant part, vector part
  -> (f, Map i f)
affineCirc2Map = \case
  ConstGate k   -> (k, Map.empty)
  Var x         -> (0, Map.singleton x 1)
  ScalarMul s c -> (s * konst, (s *) <$> vec)
    where
      (konst, vec) = affineCirc2Map c
  Add c1 c2     -> (konst1 + konst2, Map.unionWith (+) vec1 vec2)
    where
      (konst1, vec1) = affineCirc2Map c1
      (konst2, vec2) = affineCirc2Map c2

-- | Evaluate affine map at inputs
evalAffineMap :: (Num f, Ord i)
  -- | Constant part, vector part
  => (f, Map i f)
  -- | inputs
  -> Map i f
  -> f
evalAffineMap (konst, vec) inp =
  konst + dotProd' inp vec

-- A sort of dot-product on Maps.
-- @dotProd x y@ goes through each (k, v) in y, looks up the corresponding
-- (k, v') in x, computes the product v*v' (or 0 if not found in x).
-- Returns the sum of all such products.
-- dotProd :: (Num f, Ord i) => Map i f -> Map i f -> f
-- dotProd inp =
--   sum . Map.elems . Map.mapWithKey (\k v -> v * Map.findWithDefault 0 k inp)

-- | Cleaner version of @dotProd@
dotProd' :: (Num f, Ord i) => Map i f -> Map i f -> f
dotProd' vec1 vec2 = sum $ Map.intersectionWith (*) vec1 vec2

-- | subtract an affine circuit from another
sub :: Num f
  => AffineCirc i f
  -> AffineCirc i f
  -> AffineCirc i f
sub c1 c2 = Add c1 (ScalarMul (-1) c2) -- x - y = x + (-1 * y)
