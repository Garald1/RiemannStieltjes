# Status

Updated 27 November 2026.

## Done

- **Task 1 (HANDOFF.md):** the Riemann–Stieltjes library as a standalone Lake package on IEANTN's
  pins (Lean v4.34.0-rc2, Mathlib `71a80585`). It is ported from `mv-lemma-12-14` at `3992e7d7`
  (dirichlet-jordan plus the digamma, Lemma 12.14, uniform digamma bound, and Fourier integral
  theorem files).
  - `lake build`: clean, with no `sorry`.
  - `lake env lean scripts/CheckAxioms.lean`: all 1853 declarations of the package use only
    `propext`, `Classical.choice` and `Quot.sound`.
  - Changes: see `PORTING.md`.

## Open questions (for Harald)

- `Stieltjes/Unused.lean` never compiled, even in the fork. It is kept but not built: fix it or
  drop it?
- Author lines of the six new files that hold the additions to existing Mathlib files: currently
  those of the Stieltjes files. Correct?
- `mv-lemma-12-14` has moved on (`737b220f`: `NumberTheory/WeilExplicitFormula/*`, the other chat's
  proof of 12.13). Those files belong to the IEANTN solution (Task 7), not to the library; they are
  not ported.

## Next

- Task 5: the `ContourIntegration.v1` reactivation pull request (instructions of 27 November).
- Task 2, step 2, on a branch based on `reactivate-contour-integration`.
- Task 6.
