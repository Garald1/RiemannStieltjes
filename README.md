# RiemannStieltjes

The Riemann–Stieltjes integral via `BoxIntegral`, the Dirichlet–Jordan theorem, Fejér's theorem,
the Fourier integral theorem for L¹ ∩ BV(ℝ), and estimates for the digamma function
(Montgomery–Vaughan Theorem C.5 and Lemma 12.14). It is a standalone Lake package on IEANTN's Lean
and Mathlib pins, ported from the workshop fork `Garald1/mathlib-at-ICERM26`.

Module names are `RiemannStieltjes.<path in Mathlib>`. Declaration names are those of the fork, so
the library can go back into Mathlib. See `PORTING.md` and `STATUS.md`.

    lake exe cache get && lake build
