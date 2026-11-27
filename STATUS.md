# Status

Updated 27 November 2026.

## Done

- The ICERM Riemann–Stieltjes library (branch `dirichlet-jordan` of `Garald1/mathlib-at-ICERM26`)
  as a standalone Lake package on IEANTN's pins (Lean v4.34.0-rc2, Mathlib `71a80585`).
  - `lake build`: clean, with no `sorry`; `Stieltjes/Unused.lean` included, now repaired.
  - `lake env lean scripts/CheckAxioms.lean`: all 1611 declarations use only `propext`,
    `Classical.choice` and `Quot.sound`.
  - Changes: see `PORTING.md`.
- The explicit-formula material is in the separate package `Garald1/WeilExplicitFormula`, which
  requires this one.
