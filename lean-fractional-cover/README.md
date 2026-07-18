# Fractional-cover Lean formalization

This isolated subproject formalizes the finite combinatorial proof for the strict finite-k fractional-cover bound on adjacent disjoint subset-sum gaps.

The branch and draft pull request are used as a reproducible Lean 4.31.0 / mathlib 4.31.0 CI environment while the proof is completed. The project is not intended to modify the trading code in the repository.

Run locally with:

```bash
cd lean-fractional-cover
lake update
lake exe cache get
lake build
```
