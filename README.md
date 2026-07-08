# Arith(metic)-Circ(uit)

**Arith-Circ** is an embedded domain-specific language for building *arithmetic circuits*, a low-level universal model of computation. Given such a circuit, its execution on some given inputs can be provably verified very efficiently (in particular, much more efficiently than simply re-executing the circuit) with a cryptographic proof system such as [Groth16](https://eprint.iacr.org/2016/260).

```haskell
circ :: ArithCirc Fr
circ = execCircBuilder $ do
  i0 <- var <$> input
  i1 <- var <$> input
  compile2Out (mul i0 i1)
```

## Quick Usage

```haskell
import Arithmetic (ArithCirc)
import Expr (execCircBuilder)
import Lang (mul, var, input, compile2Out)
import Qap (Qap, arithCirc2Qap, Family, assignment, witness)
```
In this simple example, we'll use the above **Arith-Circ** types and functions. We'll also use an `IntMap` for specifying inputs $`i_0, i_1`$ to our circuit, which are values in the scalar field `Fr` of the [BN254 elliptic curve](https://hackmd.io/@jpw/bn254). 

```haskell
import Data.IntMap.Strict qualified as M
import ZK.Algebra.Pure.Instances.BN254 (Fr)
```

The simplest possible circuit consists of a single multiplication gate, corresponding to the product $`i_0 \times i_1`$ of two inputs

```haskell
circ :: ArithCirc Fr
circ = execCircBuilder $ do
  i0 <- var <$> input
  i1 <- var <$> input
  compile2Out (mul i0 i1)
```
Given inputs $`i_0=6, i_1=8`$, a prover executes this circuit, producing an execution trace i.e. the assignment of values to wires, in this case the two input wires and the output wire with the product $48$.

```haskell
trace :: Family Fr
trace = assignment circ ins
  where
    ins = M.fromList $ zip [0..] [6, 8]
```
To *prove* that `trace` is indeed a valid execution trace, we'll need the circuit to be represented in a form preferred by the backend proof system, namely as a quadratic arithmetic program (or more generally, a rank-1 constraint system (R1CS)).

```haskell
qap :: Qap Fr
qap = arithCirc2Qap circ
```

Then the claim that `trace` is a valid execution trace amounts to the existence of a certain polynomial $w$ witnessing this claim. The backend produces a succinct proof (more precisely, *argument*) of knowledge of such a polynomial!

```haskell
witnessPoly :: IO ()
witnessPoly =
  case witness qap trace of
    Nothing -> putStrLn "invalid trace"
    Just w  -> print w
```
## Links

See also Adjoint's [arithmetic circuits](https://github.com/sdiehl/arithmetic-circuits).
