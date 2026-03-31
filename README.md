# Formal Verification of secp256k1 modular scalar multiplication 

Standalone extraction of `secp256k1_scalar_mul` from
[bitcoin-core/secp256k1](https://github.com/bitcoin-core/secp256k1) for formal
verification with **[Rocq](https://rocq-prover.org/)** / **[Verifiable Software Toolchain](https://vst.cs.princeton.edu/)**.

## Goal

This project is a proof-of-concept showing that **formal verification of
bitcoin-core/secp256k1 is possible**. The secp256k1 library sits at the heart
of Bitcoin. Every signature check depends on it being correct. Here we take
real C code from the library and prove it correct against a mathematical
specification using Rocq and the Verified Software Toolchain (VST).

The proof covers the full pipeline of modular scalar multiplication:
multi-precision integer arithmetic, carry propagation, and modular folding
reduction modulo the curve order. All reasoning is machine-checked, yielding a
mechanized guarantee that the C implementation computes exactly 
$r \equiv a \cdot b \pmod{N}$ for all representable inputs, where $N$ is the
secp256k1 group order.

VST works by symbolic execution of the C program within separation logic,
verifying each statement against a formal precondition/postcondition contract.
When the verified C code is compiled with CompCert, its proven compiler
correctness theorem extends the guarantee all the way down to the generated
assembly.

## Scope

The verified entry point is **modular scalar multiplication** over the
secp256k1 group order $N$:

```c
void secp256k1_scalar_mul(secp256k1_scalar *r,
                          const secp256k1_scalar *a,
                          const secp256k1_scalar *b);
```

Internally this decomposes into two phases:

1. **`secp256k1_scalar_mul_512`**: schoolbook 4×4-limb multiply producing a
   full 512-bit product from two 256-bit scalars.
2. **`secp256k1_scalar_reduce_512`**: three-stage modular folding
   (512 → 385 → 258 → 256 bits) using the complement
   $C = 2^{256} - N$, followed by a final conditional subtraction.

Together with all supporting helpers (`muladd`, `extract`, `u128` emulation,
overflow check, etc.), the verified code totals roughly 300 lines of C.
The proof code across all Rocq files totals ~6,400 lines, giving a 
proof-to-code ratio of roughly **21:1**, which is typical for VST
verification of non-trivial arithmetic code.

Both functions follow the non-assembly, 64-bit, pure-C path from
[`scalar_4x64_impl.h`](https://github.com/bitcoin-core/secp256k1/blob/ffc25a2731fd277e056c6f62aa94eb0fb78e031d/src/scalar_4x64_impl.h#L680).
CompCert does not support `__int128`, so 128-bit arithmetic is emulated with a
struct of two `uint64_t` limbs, matching the upstream fallback path.

## Setup

The development environment can be set up with any of:

- **Nix** (recommended): `nix develop` (or `nix-shell`) provides Rocq 9.0, VST, CompCert, and all dependencies.
- **Dev Container**: open in VS Code with the Dev Containers extension or use `devcontainer up`.
- **[opam](https://opam.ocaml.org/)** (manual):

  ```
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam update
  opam install rocq-prover coq-vst.2.16 vsrocq-language-server
  ```

  You also need `gcc`, `libgmp-dev` (or equivalent), `m4`, and `pkg-config`
  from your system package manager.

The first run builds some packages from source and may take a while.

## Build

Run everything (library, tests, Clight extraction, proofs):

```
make
```

Or run individual stages:

| Target        | Description                                    |
|---------------|------------------------------------------------|
| `make lib`    | Build `libsecp256k1_scalar.a`                  |
| `make test`   | Build and run the unit tests                   |
| `make clight` | Extract the Clight AST (requires CompCert)     |
| `make proof`  | Build all Rocq proofs (parallel with `-j`)     |

To build with [CompCert](https://compcert.org/):

```
make CC=ccomp lib
```

On a modern AMD laptop the proofs take a few minutes. VST's separation-logic
tactics (`forward`, `entailer!`, `forward_call`) produce large proof terms,
and `lia`/`nia` is called hundreds of times.

## Trust boundary

A proof is only as good as its specification. The file
[`proof/Spec_scalar_4x64.v`](proof/Spec_scalar_4x64.v) mirrors the C header
[`src/scalar_4x64.h`](src/scalar_4x64.h). It defines the `Scalar` type, the operation `scalar_mul` ($a \cdot b \bmod N$), the C representation, and the VST function contract.
The rest of the proof code: carry lemmas, limb arithmetic, thousands of lines, is mechanically checked by Rocq. The spec file is the contract between the C world and the formal world.

## Acknowledgement 

This work is funded by the [OpenSats Initiative](https://opensats.org/).
Many thanks for supporting open-source cryptography infrastructure.

## License

The extracted C code retains its original MIT license from bitcoin-core/secp256k1.
The Rocq proof files under `proof/` are licensed under
[GPL-3.0-or-later](https://www.gnu.org/licenses/gpl-3.0.html).
