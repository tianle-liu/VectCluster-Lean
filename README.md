# VectCluster-Lean

Lean 4 proofs for the main theorems of Haoyang Liu and Tianle Liu,
[*Algebraic Vector Bundles on Cluster Varieties*](https://arxiv.org/abs/2610.12748).

## Main results

The paper works over a perfect field of characteristic different from two.

- **Theorem A:** every algebraic vector bundle on a cluster variety with principal
  coefficients at an acyclic seed of irreducible finite Dynkin type is trivial.
  See [`PrincipalFiniteDynkinBundles.all_free`](Verification/PrincipalFiniteDynkinBundles.lean).
- **Theorem B:** the specified smooth cluster sevenfold admits an indecomposable
  rank-two bundle that becomes free after adding one trivial line.
  See [`SevenfoldMainCounterexample.exists_bundle`](Verification/SevenfoldMainCounterexample.lean).

The Lean statements retain explicit reference-theory hypotheses. The cited
background theories are supplied as inputs rather than re-proved here; their
existence and applicability are not established by these conditional proofs.
This repository contains A, B, and their dependencies, rather than the entire
paper's formalization.

## Build

The project uses **Lean 4.19.0** and **mathlib v4.19.0**.
Install [Lean through elan](https://leanprover-community.github.io/get_started.html), then run:

```sh
git clone https://github.com/tianle-liu/VectCluster-Lean.git
cd VectCluster-Lean
lake exe cache get
lake build MainTheorems
```

[`MainTheorems.lean`](MainTheorems.lean) imports both final theorems and displays
their types and axiom dependencies. The proof modules are in [`Verification/`](Verification/).
Compiler and dependency versions are fixed in `lean-toolchain` and `lake-manifest.json`.

## Citation

```bibtex
@misc{LiuLiu2026,
  author        = {Haoyang Liu and Tianle Liu},
  title         = {Algebraic Vector Bundles on Cluster Varieties},
  year          = {2026},
  eprint        = {2610.12748},
  archivePrefix = {arXiv},
  primaryClass  = {math.AG},
  url           = {https://arxiv.org/abs/2610.12748}
}
```

See [CONTRIBUTING.md](CONTRIBUTING.md) for contribution guidelines.
Released under the [Apache License 2.0](LICENSE).
