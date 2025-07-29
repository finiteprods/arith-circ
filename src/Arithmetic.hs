{-# LANGUAGE LambdaCase, StrictData #-}

module Arithmetic where

import Data.Bits (testBit, Bits (testBit))
import Data.Foldable (foldl')
import Affine (AffineCirc(..), collectInputsAffine, evalAffineCirc, mapVarsAffine)
import ZK.Algebra.API (PrimeField, asInteger)
import GHC.Stack (HasCallStack)

-- | wire with int label
data Wire
  = Input Int
  | Intermediate Int
  | Output Int
  deriving (Show, Eq, Ord)

-- --> G --> ... --> G -->
-- Inp  Intm     Intm  Out


-- | gate with "ports" of type i and values of type f flowing through it
data Gate i f
  -- | "singleton" arithmetic circuit consisting of a single mult gate
  = Mul
      { mulL :: AffineCirc i f
      , mulR :: AffineCirc i f
      , mulO :: i
      }
  | Equal
      { eqIn    :: i
      , eqMagic :: i
      , eqOut   :: i
      }
  | Split -- fan-out?
      { splitIn   :: i
      , splitOuts :: [i]
      }
  deriving (Show, Eq)

-- is this used? see @inputWires@
collectInputsGate :: Gate i f -> [i]
collectInputsGate = \case
  Mul l r _ -> collectInputsAffine l ++ collectInputsAffine r
  _nonMul   -> error "collectInputsGate: only supports multiplication gates"

-- | list input wires of a gate
inputWires :: Gate i f -> [i]
inputWires = \case
  Mul l r _     -> collectInputsAffine l ++ collectInputsAffine r
  Equal inp _ _ -> [inp] -- ignore magic wire, filled in when evaluating circ
  Split inp _   -> [inp]

-- | list output wires of a gate
outputWires :: Gate i f -> [i]
outputWires = \case
  Mul _ _ out   -> [out]
  Equal _ _ out -> [out]
  Split _ outs  -> outs

-- | rename variables (ideally f is injective)
mapVarsGate :: (i -> j) -> Gate i f -> Gate j f
mapVarsGate f = \case
  Mul l r o   -> Mul (mapVarsAffine f l) (mapVarsAffine f r) (f o)
  Equal i m o -> Equal (f i) (f m) (f o)
  Split i os  -> Split (f i) (map f os)

-- | evaluate an arithmetic gate
evalGate :: (PrimeField f, HasCallStack)
  -- | wire variable lookup logic
  => (i -> vars -> Maybe f)
  -- | wire variable update logic
  -> (i -> f -> vars -> vars)
  -- | environment before evaluation
  -> vars
  -- | gate to evaluate
  -> Gate i f
  -- | environment after evaluation
  -> vars

evalGate lkp upd env = \case
  Mul l r out ->
    let val = evalAffineCirc lkp env l * evalAffineCirc lkp env r
    in upd out val env
  Equal i m out ->
    case lkp i env of
      Nothing -> error "evalGate: couldn't lookup in-wire of Equal gate"
      Just v  ->
        let (val, mid) = if v == 0 then (0, 0) else (1, recip v)
        in upd out val $ upd m mid env
  Split i outs ->
    case lkp i env of
      Nothing -> error "evalGate: couldn't lookup in-wire of Split gate"
      Just v  ->
        snd $ foldl' setOutWire (0, env) outs
          where
            -- updates @env'@ with @out@ indicating if @ix@th bit of @v@ set
            setOutWire (ix, env') out =
              (ix + 1, upd out (isSet ix v) env')
            -- returns whether @j@th bit of @fldElt@ is set
            isSet j fldElt = bool2Val $ testBit (asInteger fldElt) j
            bool2Val b = if b then 1 else 0

-- | a (valid) arithmetic circuit consists of a list of gates g
--   where any in-wire of g is either @Input@
--   or an @Intermediate@ out-wire of a gate appearing earlier in the list
newtype ArithCirc f = ArithCirc { unArithCirc :: [Gate Wire f] }
  deriving (Eq, Show)

-- | check wire configuration of circuit
validArithCirc :: ArithCirc f -> Bool
validArithCirc (ArithCirc gates) =
  fst $ foldl' accDefinedWires (True, []) gates
    where
      accDefinedWires (valid, definedWires) gate =
        let outWires = outputWires gate in
          ( valid
              && all notInputWire outWires
              && all (validWire definedWires) (inputWires gate),
            definedWires ++ outWires
          )
      notInputWire  = \case { Input _ -> False; _notInput -> True }
      validWire dws = \case
        Input _             -> True
        Output _            -> False
        iw@(Intermediate _) -> iw `elem` dws

-- | generate (effectfully) values for a gate... how many?
--   Mul:   1
--   Equal: 2
--   Split: n + 1 where n is the no. out-wires
genValuesGate :: Applicative m => m f -> Gate i f -> m [f]
genValuesGate gen = \case
  Mul {}       -> pure <$> gen
  Equal {}     -> (\x y -> [x, y]) <$> gen <*> gen
  Split _ outs -> (:) <$> gen <*> traverse (const gen) outs

genValuesCirc :: Applicative m => m f -> ArithCirc f -> m [[f]]
genValuesCirc gen = traverse (genValuesGate gen) . unArithCirc

-- | update environment by evaluating a circuit
evalArithCirc :: forall f vars. PrimeField f -- TODO check why forall
  -- | wire lookup logic
  => (Wire -> vars -> Maybe f)
  -- | wire update logic
  -> (Wire -> f -> vars -> vars)
  -- | circuit to evaluate
  -> ArithCirc f
  -- | environment containing inputs
  -> vars
  -- | environment containing inputs, intermediates, outputs
  -> vars

evalArithCirc lkp upd (ArithCirc gs) env =
  foldl' (evalGate lkp upd) env gs

-- | converts a binary representation into a formal linear combination
unsplit :: Num f
  -- | bit-wires representing a number in little-endian
  => [Wire]
  -- | affine circuit computing the linear combination
  -> AffineCirc Wire f
unsplit = snd . foldl' addTerm (0 :: Integer, ConstGate 0)
  where
    addTerm (i, circ) bitwire =
      ( i + 1,
        circ `Add` ScalarMul (2 ^ i) (Var bitwire)
      )
