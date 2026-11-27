# Porting notes

Source: branch `mv-lemma-12-14` of `Garald1/mathlib-at-ICERM26` at `3992e7d7`, which is
`dirichlet-jordan` (`90f274f8`) plus the digamma and Fourier-integral commits. That fork is on
Lean v4.30.0-rc2. Target: Lean `v4.34.0-rc2` and Mathlib `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`
(IEANTN's pins).

The first commit of this repository is the verbatim copy, with only the imports rewritten, so
`git diff 4771575 -- RiemannStieltjes` shows every porting change.

## Layout

- `Mathlib/X.lean` of the fork becomes `RiemannStieltjes/X.lean`, module `RiemannStieltjes.X`.
  Namespaces and declaration names are unchanged (exceptions below).
- The fork's additions to six existing Mathlib files (`BoxIntegral/Basic`,
  `BoxIntegral/Partition/{Additive,Basic,Filter,Measure,Split}`) are new files with the same paths
  under `RiemannStieltjes/`. Each imports the Mathlib original plus the package's versions of
  whichever of the six that original imports. They carry the author list of the Stieltjes files
  (Creech, de Dios, Georgiev, Helfgott, Khaitan, Tao); **to be confirmed by Harald**.
- Not ported: the two-line `Set.Ioc` qualification in `Partition/Basic.lean`, and the
  `DivergenceTheorem` fixes of `mv-lemma-12-14`, both needed only inside the fork.
- `Stieltjes/Unused.lean` is in the repository but **not in the build**: it never compiled in the
  fork either (it uses `F`, `a`, `b` without declaring them, and the unknown `val_eq_of_eq`).

## Kinds of change

1. **`convert` closes fewer goals.** Mathlib's `convert` now tries `rfl` on the remaining goals only
   at reducible transparency (`Convert.CheapConfig`, `postTransparency := .reducible`), so goals
   like `addCommGroup = instNormedAddCommGroup.toAddCommGroup` or `c • g = ⇑(lsmul ℝ ℝ c) ∘ g` are
   left open. Fix: `convert` → `convert!`, the old behaviour. This was done throughout the files
   that had such failures: `Stieltjes/{Basic,IntegrationByParts,Riemann,ChangeVariables,Measure,
   Fourier,Sum,FourierIntegral,DigammaPairing}` and, at the failing sites only,
   `Gamma/{DigammaSeries,DigammaFourier}`.
2. **Upstreamed to Mathlib, so removed here:** `BoxIntegral.integralSum_congr`,
   `BoxIntegral.hasIntegral_congr` (same statements), `intervalIntegral.integral_congr_uIoo`
   (now needs only `NullSingletonClass`), and `MonotoneOn.eVariationOn_eq`, `eVariationOn_id`,
   `eVariationOn_id_Icc`. The last three dropped the hypothesis `a ≤ b`, and `eVariationOn_id_Icc`
   now takes `a b` explicitly. Call sites were adjusted.
3. **Name clash, renamed:** `MonotoneOn.boundedVariationOn` (ours: `MonotoneOn f (Icc a b)` gives
   `BoundedVariationOn f (Icc a b)`) became **`MonotoneOn.boundedVariationOn_Icc`**. Mathlib now has
   `MonotoneOn.boundedVariationOn` for any set, assuming a bound on `|f|`.
4. **Renames and signature changes in Mathlib:** `intervalIntegral.intervalIntegrable_const` →
   `intervalIntegrable_const`. `integrableOn_rpow_mul_exp_neg_mul_rpow` now assumes `0 < p`
   instead of `1 ≤ p` (`le_rfl` → `one_pos`). `ContinuousLinearMap.sub_apply` no longer takes the
   maps explicitly (`(B _).sub_apply` → `ContinuousLinearMap.sub_apply`). `sum_apply` is now
   ambiguous between `_root_` and `Finset` (→ `Finset.sum_apply`).
5. **`NNReal` built with `⟨r, h⟩`.** Mathlib warns against the anonymous constructor for `ℝ≥0`,
   and current Lean no longer unifies `Subtype.mk` terms with `ℝ≥0` patterns when rewriting.
   Fix: `NNReal.mk r h`, keeping `nndist` folded, or `rw` instead of `simp` (`Partition/Filter`).
6. **Membership in a `Prepartition` written as a structure instance.** `simp [mem_mk, mem_image]`
   now unfolds `J ∈ {boxes := s.image f, ..}` to a `Quot.lift` on the underlying multiset.
   Fix: restate membership by definitional equality (`show J ∈ s.image f from h`) and use
   `Finset.mem_image` (`Partition/Onedim`, `Stieltjes/ChangeVariables`).
7. **Local proof repairs** where `simp`, `grind`, `grw`, `field_simp` or `fun_prop` now behave
   differently: a few `simp` calls need `Box.upper₁`/`Box.lower₁` (or a `let`) unfolded; two
   `grind` calls replaced by short explicit arguments; `grw` with a strict inequality under a
   product replaced by a `calc`; `fun_prop` given the function explicitly; one goal that
   `field_simp` now leaves as `≤` (formerly `<`) closed with `le_of_lt`.

No statement was changed, apart from the deletions and the rename above.

85 warnings remain (deprecations, unused `simp` arguments, style linters). They are left alone, to
keep the diff small.
