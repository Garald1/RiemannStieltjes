# RiemannStieltjes

The Riemann–Stieltjes integral via `BoxIntegral`, (Montgomery–Vaughan, Appendix A), Fejér's theorem
and the Dirichlet–Jordan theorem for Fourier series. It is a standalone Lake package on IEANTN's Lean
and Mathlib pins, ported from the workshop fork `Garald1/mathlib-at-ICERM26`.

Module names are `RiemannStieltjes.<path in Mathlib>`. Declaration names are those of the fork, so
the library can go back into Mathlib. See `PORTING.md` and `STATUS.md`.

    lake exe cache get && lake build
