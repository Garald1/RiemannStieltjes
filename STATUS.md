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

## Done since

- Task 5 (reactivation): branch `reactivate-contour-integration` of `Garald1/IEANTN`, with
  fingerprints added and the author reset; pull request teorth/IEANTN#288.

## Next

- HANDOFF.md at `c736b04` splits Task 1 into two packages. This package keeps only the ICERM
  material; the five files `Gamma/{DigammaSeries,DigammaFourier}` and
  `Stieltjes/{VariationBounds,DigammaPairing,FourierIntegral}` move to a second package
  `WeilExplicitFormula` (name to be confirmed), together with the eight
  `NumberTheory/WeilExplicitFormula/*` files from `mv-lemma-12-14`. Both repositories are to be
  public.
- Task 2, step 2, on a branch based on `reactivate-contour-integration`.
- Task 7 (the IEANTN solutions, by unfolding).
