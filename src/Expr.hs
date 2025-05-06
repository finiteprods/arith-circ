{-# LANGUAGE GADTs, LambdaCase #-}

module Expr where

import ZK.Algebra.Class.Field (PrimeField)
import GHC.Stack (HasCallStack)
import Control.Monad.State (State, execState, runState, gets, modify)
import Control.Monad (join)
import Arithmetic
import Data.Bifunctor (first, second)
import Affine

-- | Unary operator `a` -> `a`
data UnOp f a where
  UNeg :: UnOp f f
  UNot :: UnOp f Bool
  -- | # truncate bits, rotate bits
  -- URot :: Int -> Int -> UnOp f f -- TODO

-- | Binary operator `a` -> `a` -> `a`
data BinOp f a where
  BAdd :: BinOp f f
  BSub :: BinOp f f
  BMul :: BinOp f f
  BAnd :: BinOp f Bool
  BOr  :: BinOp f Bool
  BXor :: BinOp f Bool

-- | Arithmetic expressions of type @t@ over a field @f@
-- with variable names/indices coming from @i@
data Expr i f t where
  -- | Constant field element
  EConst     :: f -> Expr i f f
  EConstBool :: Bool -> Expr i f Bool
  -- | Field variable
  EVar       :: i -> Expr i f f
  EVarBool   :: i -> Expr i f Bool
  -- | Unary operation over a subexpression
  EUnOp      :: UnOp f t -> Expr i f t -> Expr i f t
  EBinOp     :: BinOp f t -> Expr i f t -> Expr i f t -> Expr i f t
  EIf        :: Expr i f Bool -> Expr i f t -> Expr i f t -> Expr i f t
  -- | Equality of two subexpressions
  EEq        :: Expr i f f -> Expr i f f -> Expr i f Bool

deriving instance (Show i, Show f) => Show (Expr i f t)
deriving instance (Show f)         => Show (BinOp f a)
deriving instance (Show f)         => Show (UnOp f a)

-- | Evaluate arithmetic expressions given an environment
evalExpr :: (PrimeField f, HasCallStack)
  -- | variable lookup logic
  => (i -> vars -> Maybe f)
  -- | expression to eval
  -> Expr i f t
  -- | environment
  -> vars
  -- | resulting value
  -> t

evalExpr lkp expr env = case expr of
  EConst f     -> f
  EConstBool b -> b
  EVar i       ->
    case lkp i env of
      Just v  -> v
      Nothing -> error "evalExpr: incorrect variable lookup"
  EVarBool i   ->
    case lkp i env of
      Just f  -> f == 1
      Nothing -> error "evalExpr: incorrect variable lookup"
  EUnOp UNeg e -> negate $ evalExpr lkp e env
  EUnOp UNot e -> not    $ evalExpr lkp e env
  EBinOp bop e1 e2 ->
    case bop of
      BAdd -> v1 + v2
      BSub -> v1 - v2
      BMul -> v1 * v2
      BAnd -> v1 && v2
      BOr  -> v1 || v2
      BXor -> v1 /= v2 -- (v1 || v2) && not (v1 && v2)
      where
        v1 = evalExpr lkp e1 env
        v2 = evalExpr lkp e2 env
  EIf e1 e2 e3 ->
    if evalExpr lkp e1 env
      then evalExpr lkp e2 env
      else evalExpr lkp e3 env
  EEq e1 e2 ->
    evalExpr lkp e1 env == evalExpr lkp e2 env

-- | Rename variables.
mapVarExpr :: (i -> j) -> Expr i f t -> Expr j f t
mapVarExpr f = \case
  EConst k        -> EConst k
  EConstBool b    -> EConstBool b
  EVar x          -> EVar (f x)
  EVarBool x      -> EVarBool (f x)
  EUnOp op e      -> EUnOp op (mapVarExpr f e)
  EBinOp op e1 e2 -> EBinOp op (mapVarExpr f e1) (mapVarExpr f e2)
  EIf e1 e2 e3    -> EIf (mapVarExpr f e1) (mapVarExpr f e2) (mapVarExpr f e3)
  EEq e1 e2       -> EEq (mapVarExpr f e1) (mapVarExpr f e2)

-- | arithmetic circuit builder
type ExprM f a = State (ArithCirc f, Int) a

reverseCirc :: ArithCirc f -> ArithCirc f
reverseCirc = ArithCirc . reverse . unArithCirc

-- | take a circuit builder and actually build it
runCircBuilder :: ExprM f a -> (a, ArithCirc f)
-- NOTE analogous to State monad's runState but drops Int from (ArithCirc f, Int)
-- why reverse the circuit? gates are emitted by consing i.e. in reverse order
runCircBuilder = second (reverseCirc . fst) . flip runState (ArithCirc [], 0)

-- | one half of @runCircBuilder@
execCircBuilder :: ExprM f a -> ArithCirc f
execCircBuilder = reverseCirc . fst . flip execState (ArithCirc [], 0)

-- | one half of @runCircBuilder@
evalCircBuilder :: ExprM f a -> a
evalCircBuilder = fst . runCircBuilder

-- | increment "fresh variable counter" part of state
fresh :: ExprM f Int
fresh = do
  v <- gets snd
  modify $ second (+ 1)
  return v

-- | expand circuit part of state with a gate
emit :: Gate Wire f -> ExprM f ()
emit g = modify . first $ ArithCirc . (g :) . unArithCirc

-- | new input / intermediate / output wire
newIn, newMid, newOut :: ExprM f Wire
newIn  = Input        <$> fresh
newMid = Intermediate <$> fresh
newOut = Output       <$> fresh

-- | "downcast right"
either2Aff :: Either Wire (AffineCirc Wire f) -> AffineCirc Wire f
either2Aff (Left w)  = Var w
either2Aff (Right c) = c

-- | "downcast left" emits a multiplication gate
either2Wire :: Num f => Either Wire (AffineCirc Wire f) -> ExprM f Wire
either2Wire (Left w)  = pure w
either2Wire (Right c) = do
  mulOut <- newMid
  emit $ Mul (ConstGate 1) c mulOut
  pure mulOut

-- | emit multiplication gate and return its out-wire
eitherProd
  :: Either Wire (AffineCirc Wire f)
  -> Either Wire (AffineCirc Wire f)
  -> ExprM f Wire
eitherProd l r = do
  mulOut <- newMid
  emit $ Mul (either2Aff l) (either2Aff r) mulOut
  pure mulOut

-- | compile expression into either:
-- an affine circuit
-- or the out-wire of a non-affine circuit
compile :: Num f
  => Expr Wire f t
  -> ExprM f (Either Wire (AffineCirc Wire f))
compile = \case
  EConst n     -> pure . Right . ConstGate $ n
  EConstBool b -> pure . Right . ConstGate $ if b then 1 else 0
  EVar v       -> pure $ Left v
  EVarBool v   -> pure $ Left v
  EUnOp op e   -> case op of
    -- | not b := 1 - b
    UNot -> Right . sub (ConstGate 1) . either2Aff <$> compile e
    UNeg -> Right . ScalarMul (-1)    . either2Aff <$> compile e
  EBinOp op e1 e2 -> case op of
    BAdd -> liftA2 Add <$> compile e1 <*> compile e2
    BSub -> liftA2 sub <$> compile e1 <*> compile e2
    BMul -> Left <$> join (eitherProd <$> compile e1 <*> compile e2)
    BAnd -> fmap Left =<< eitherProd <$> compile e1 <*> compile e2 -- TODO or patterns ghc9.12
    -- | or b b' := b + b' - b * b'
    BOr  -> do
      wc1 <- compile e1
      wc2 <- compile e2
      Right . sub (either2Aff wc1 `Add` either2Aff wc2) . Var <$> eitherProd wc1 wc2
    -- | xor b b' := b + b' - 2 * b * b'
    BXor -> do
      wc1 <- compile e1
      wc2 <- compile e2
      Right
        . Add (either2Aff wc1 `Add` either2Aff wc2)
        . ScalarMul (-2)
        . Var <$> eitherProd wc1 wc2
  -- | if b x y := b * x + (1 - b) * y
  EIf e1 e2 e3 -> do
    wc1 <- compile e1
    wc2 <- compile e2
    wc3 <- compile e3
    fmap Right $ Add
      <$> fmap Var (eitherProd wc1 wc2)
      <*> fmap Var (eitherProd (sub (ConstGate 1) <$> wc1) wc3)
  --  liftA2 Add . Right . Var
  --    <$> mulEithers wc1 wc2
  --    <*> fmap (Right . Var) (mulEithers (sub (ConstGate 1) <$> wc1) wc3)
  -- | eq x y := 1 - 0/=(x - y)
  EEq e1 e2 -> do
    diff  <- liftA2 sub <$> compile e1 <*> compile e2
    eqOut <- newMid
    emit =<< Equal <$> either2Wire diff <*> newMid <*> pure eqOut
    pure . Right . sub (ConstGate 1) $ Var eqOut
