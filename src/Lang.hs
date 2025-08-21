{-# LANGUAGE LambdaCase #-}
module Lang where

import Expr
import Arithmetic (Wire, Gate (Mul))
import Affine (AffineCirc(ConstGate))

-- | lift constant to expression
k :: f -> Expr Wire f f
k = EConst

-- | binary arithmetic on expressions
add, sub, mul :: Expr Wire f f -> Expr Wire f f -> Expr Wire f f
add = EBinOp BAdd
sub = EBinOp BSub
mul = EBinOp BMul

-- | binary bool logic on expressions
band, bor, bxor :: Expr Wire f Bool -> Expr Wire f Bool -> Expr Wire f Bool
band = EBinOp BAnd
bor  = EBinOp BOr
bxor = EBinOp BXor

bnot :: Expr Wire f Bool -> Expr Wire f Bool
bnot = EUnOp UNot

eq :: Expr Wire f f -> Expr Wire f f -> Expr Wire f Bool
eq = EEq

-- | lift wire to "variable expression"
var :: Wire -> Expr Wire f f
var = EVar

cond :: Expr Wire f Bool -> Expr Wire f t -> Expr Wire f t -> Expr Wire f t
cond = EIf

input :: ExprM f Wire
input = newIn

-- | compile expression to wire
-- * if compiles to wire, done
-- * otherwise emit gate with out-wire the given new wire
compile2Wire :: Num f => ExprM f Wire -> Expr Wire f f -> ExprM f Wire
compile2Wire newWire e = do
  compile e >>= \case
    Left w  -> pure w
    Right c -> do
      w <- newWire
      emit $ Mul (ConstGate 1) c w
      pure w

compile2Mid :: Num f => Expr Wire f f -> ExprM f Wire
compile2Mid = compile2Wire newMid

compile2Out :: Num f => Expr Wire f f -> ExprM f Wire
compile2Out = compile2Wire newOut
