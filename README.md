This repository contains a formal model of the EVM and Yul in Lean 4.
Where applicable, the underlying EVM primops are used directly by the Yul model.

Everything here is work in progress and is subject to change therefore.

# Requirements
- Python packages: coincurve, typing-extensions, pycryptodome, eth-typing, py-ecc

# Project structure

## Primops
The `Operation` describing all of the primitive operations:
```
EvmYul/Operations.lean
```

The semantic function `primCall` associated with the ADT:
```
EvmYul/Yul/PrimOps.lean
```

## EVM
The model of the EVM state `EVM.State`:
```
EvmYul/EVM/State.lean
```

The semantic function `step`:
```
EvmYul/EVM/Semantics.lean
```

## Yul
The ADT `Stmt` mutually defined with `Expr` and `FunctionDefinition` describing Yul:
```
EvmYul/Yul/Ast.lean
```

The model of the Yul state `YUL.State`:
```
EvmYul/Yul/State.lean
```

The semantic function `exec` mutually defined with `eval` (and some misc. functions):
```
EvmYul/Yul/Interpreter.lean
```

## Conformance testing
A git submodule with EVM conformance tests is in:
```
EthereumTests/
```

The test running infrastructure can be found in:
```
Conform/
```

To execute conformance tests, make sure the `EthereumTests` directory is the appropriate git submodule and run:
```
lake test -- <NUM_THREADS> 2> out_discard.txt
```
where `<NUM_THREADS>` is the number of threads running conformance tests in parallel. Note that the default is `1`.
We recommend redirecting `stderr` into a file to not pollute the output.

## Building the project

Install `elan` to manage the Lean toolchain:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

After installation, build the project using `lake`:

```bash
lake build
```

## Simple example compiler

The file `EvmYul/SimpleCompiler.lean` contains a minimal compiler from a tiny
fragment of Yul into a toy EVM machine together with correctness lemmas. The
compiler supports literals, variables and the `ADD` operation as well as simple
assignment statements.
