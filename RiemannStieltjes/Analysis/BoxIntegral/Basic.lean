/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic
public import RiemannStieltjes.Analysis.BoxIntegral.Partition.Filter
public import RiemannStieltjes.Analysis.BoxIntegral.Partition.Measure

import Mathlib.Tactic.Peel

/-!
# Additions to `Mathlib.Analysis.BoxIntegral.Basic`

* congruence lemmas for `integralSum` and `HasIntegral`;
* the standard (mesh-size) description of the Riemann integral;
* linearity of `BoxIntegral.HasIntegral` in the volume, intertwining by continuous linear maps,
  and additivity along a partition.
-/

@[expose] public section

open scoped Topology NNReal Filter Uniformity BoxIntegral

open Set Finset Function Filter Metric BoxIntegral.IntegrationParams

noncomputable section

namespace BoxIntegral

universe u v w

variable {ι : Type u} {E : Type v} {F : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {I J : Box ι} {π : TaggedPrepartition I}

open TaggedPrepartition

local notation "ℝⁿ" => ι → ℝ

theorem integralSum_congr {f₁ f₂ : ℝⁿ → E} {vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F}
  (hf : EqOn f₁ f₂ I.Icc) (hvol : EqOn vol₁ vol₂ π.boxes) :
    integralSum f₁ vol₁ π = integralSum f₂ vol₂ π := by
  unfold integralSum
  refine Finset.sum_congr rfl (fun J hJ ↦ ?_)
  congr 1
  · exact hvol hJ
  exact hf (π.tag_mem_Icc J)

variable [Fintype ι]

theorem hasIntegral_congr (I : Box ι) (l : IntegrationParams) {f₁ f₂ : ℝⁿ → E}
    {vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F}
    (hf : EqOn f₁ f₂ I.Icc) (hvol : EqOn vol₁ vol₂ (Set.Iic I)) (y : F) :
    HasIntegral I l f₁ vol₁ y ↔ HasIntegral I l f₂ vol₂ y := by
  unfold HasIntegral
  refine Filter.tendsto_congr (fun π ↦ integralSum_congr hf (hvol.mono ?_))
  intro J hJ
  simp [π.le_of_mem' J hJ]

variable {l : IntegrationParams} {f g : (ι → ℝ) → E} {vol : ι →ᵇᵃ E →L[ℝ] F} {y y' : F}

/-! ### Standard description of the Riemann integral

Shows that the Riemann integral defined via `BoxIntegral` matches the textbook definition
-/

theorem HasIntegral_Riemann_iff (L : F) :
    HasIntegral I Riemann f vol L ↔ ∀ ε > 0, ∃ δ > 0, ∀ π : TaggedPrepartition I,
    π.IsHenstock → π.IsPartition → π.mesh_size ≤ δ → dist (integralSum f vol π) L < ε := by
  simp only [HasIntegral, tendsto_iff_eventually, Riemann_toFilteriUnion_eventually_iff_mesh,
  TaggedPrepartition.isPartition_iff_iUnion_eq]
  refine ⟨ fun h ε εpos ↦ ?_, fun h p hp ↦ ?_ ⟩
  · have : ∀ᶠ y in nhds L, dist y L < ε := by
      simp only [Metric.eventually_nhds_iff, gt_iff_lt]
      refine ⟨ ε, εpos, by simp ⟩
    specialize h this
    peel h with δ δpos hδ
    peel hδ with π hπ
    intro hhen hunion hmesh; apply hπ
    simp [hhen, hunion, hmesh]
  simp only [Metric.eventually_nhds_iff, gt_iff_lt] at hp
  obtain ⟨ ε, εpos, hε ⟩ := hp
  obtain ⟨ δ, δpos, hδ ⟩ := h ε εpos
  exact ⟨ ⟨δ, le_of_lt δpos⟩, δpos, fun π ⟨ hmesh, hhen, hunion ⟩ ↦
    hε (hδ π hhen (by simp [hunion]) hmesh) ⟩

end BoxIntegral

namespace BoxIntegral

/-! ## Linearity of `BoxIntegral.HasIntegral` in the volume
-/

variable {ι : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {I : Box ι} {l : IntegrationParams}

@[simp]
theorem integralSum_zero_vol (f : (ι → ℝ) → E) (π : TaggedPrepartition I) :
    integralSum f (0 : ι →ᵇᵃ E →L[ℝ] F) π = 0 := by
  simp [integralSum]

@[simp]
theorem integralSum_add_vol (f : (ι → ℝ) → E) (vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    integralSum f (vol₁ + vol₂) π = integralSum f vol₁ π + integralSum f vol₂ π := by
  simp [integralSum, BoxAdditiveMap.add_apply, ContinuousLinearMap.add_apply,
    Finset.sum_add_distrib]

@[simp]
theorem integralSum_neg_vol (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    integralSum f (-vol) π = -integralSum f vol π := by
  simp [integralSum, BoxAdditiveMap.neg_apply, ContinuousLinearMap.neg_apply,
    Finset.sum_neg_distrib]

@[simp]
theorem integralSum_sub_vol (f : (ι → ℝ) → E) (vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    integralSum f (vol₁ - vol₂) π = integralSum f vol₁ π - integralSum f vol₂ π := by
  simp [integralSum, BoxAdditiveMap.sub_apply, ContinuousLinearMap.sub_apply,
    Finset.sum_sub_distrib]

@[simp]
theorem integralSum_smul_vol (c : ℝ) (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    integralSum f (c • vol) π = c • integralSum f vol π := by
  simp [integralSum, BoxAdditiveMap.smul_apply, ContinuousLinearMap.smul_apply,
    Finset.smul_sum]

variable [Fintype ι] {f : (ι → ℝ) → E}

@[simp]
theorem hasIntegral_zero_vol : HasIntegral I l f (0 : ι →ᵇᵃ E →L[ℝ] F) 0 := by
  unfold HasIntegral
  rw [funext (integralSum_zero_vol f) (g := (0 : TaggedPrepartition I → F))]
  exact tendsto_const_nhds

theorem HasIntegral.add_vol {vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F} {y₁ y₂ : F}
    (h₁ : HasIntegral I l f vol₁ y₁) (h₂ : HasIntegral I l f vol₂ y₂) :
    HasIntegral I l f (vol₁ + vol₂) (y₁ + y₂) := by
  unfold HasIntegral at h₁ h₂ ⊢
  rw [funext (integralSum_add_vol f vol₁ vol₂)]
  exact h₁.add h₂

theorem HasIntegral.neg_vol {vol : ι →ᵇᵃ E →L[ℝ] F} {y : F}
    (h : HasIntegral I l f vol y) : HasIntegral I l f (-vol) (-y) := by
  unfold HasIntegral at h ⊢
  rw [funext (integralSum_neg_vol f vol)]
  exact h.neg

theorem HasIntegral.sub_vol {vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F} {y₁ y₂ : F}
    (h₁ : HasIntegral I l f vol₁ y₁) (h₂ : HasIntegral I l f vol₂ y₂) :
    HasIntegral I l f (vol₁ - vol₂) (y₁ - y₂) := by
  simpa only [sub_eq_add_neg] using h₁.add_vol h₂.neg_vol

theorem HasIntegral.smul_vol {vol : ι →ᵇᵃ E →L[ℝ] F} {y : F}
    (h : HasIntegral I l f vol y) (c : ℝ) :
    HasIntegral I l f (c • vol) (c • y) := by
  unfold HasIntegral at h ⊢
  rw [funext (integralSum_smul_vol c f vol)]
  exact (tendsto_const_nhds : Filter.Tendsto _ _ (nhds c)).smul h

/-! ### Intertwining `HasIntegral` by continuous linear maps -/

/-- If `φ : E →L[ℝ] E'` acts on integrands and `ψ : F →L[ℝ] F'` acts on integrated values, and
`vol` and `vol'` are intertwined by these two maps, then `HasIntegral` transports along
`(φ, ψ)` in the natural fashion. -/
theorem HasIntegral.map {E' F' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {vol : ι →ᵇᵃ E →L[ℝ] F} {vol' : ι →ᵇᵃ E' →L[ℝ] F'} {y : F}
    (φ : E →L[ℝ] E') (ψ : F →L[ℝ] F')
    (hvol : ∀ (J : Box ι) (e : E), ψ (vol J e) = vol' J (φ e))
    (h : HasIntegral I l f vol y) :
    HasIntegral I l (fun x ↦ φ (f x)) vol' (ψ y) := by
  have hSum : ∀ π : TaggedPrepartition I,
      integralSum (fun x ↦ φ (f x)) vol' π = ψ (integralSum f vol π) := fun π ↦ by
    simp only [integralSum, map_sum]
    exact Finset.sum_congr rfl fun J _ ↦ (hvol J (f (π.tag J))).symm
  unfold HasIntegral at h ⊢
  exact ((ψ.continuous.tendsto y).comp h).congr fun π ↦ (hSum π).symm

/-- Existence version of `HasIntegral.map`. -/
theorem Integrable.map {E' F' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {vol : ι →ᵇᵃ E →L[ℝ] F} {vol' : ι →ᵇᵃ E' →L[ℝ] F'}
    (φ : E →L[ℝ] E') (ψ : F →L[ℝ] F')
    (hvol : ∀ (J : Box ι) (e : E), ψ (vol J e) = vol' J (φ e))
    (h : Integrable I l f vol) : Integrable I l (fun x ↦ φ (f x)) vol' :=
  (h.hasIntegral.map φ ψ hvol).integrable

/-- Function-level version of `HasIntegral.map`. -/
theorem integral_map {E' F' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {vol : ι →ᵇᵃ E →L[ℝ] F} {vol' : ι →ᵇᵃ E' →L[ℝ] F'}
    (φ : E →L[ℝ] E') (ψ : F →L[ℝ] F')
    (hvol : ∀ (J : Box ι) (e : E), ψ (vol J e) = vol' J (φ e))
    (h : Integrable I l f vol) :
    integral I l (fun x ↦ φ (f x)) vol' = ψ (integral I l f vol) := by
  rw [(h.hasIntegral.map φ ψ hvol).integral_eq, h.hasIntegral.integral_eq]

/-! ### Additivity along a partition -/

/-- Box-integral additivity along a partition: if `π : Prepartition I` is a partition of `I`,
`f` is integrable on `I`, and `f` has integral `y J` over each sub-box `J ∈ π.boxes`, then `f`
has integral `∑ J ∈ π.boxes, y J` over `I`.

This is the dual of `HasIntegral.sum`, but now one decomposes the box rather than the integrand.

TODO: Show that `Integrable I` is equivalent to `∀ J ∈ π.boxes, Integrable J` via gauge gluing. -/
theorem HasIntegral.sum_of_isPartition [CompleteSpace F] {π : Prepartition I} (hπ : π.IsPartition)
    {vol : ι →ᵇᵃ E →L[ℝ] F} (hI : Integrable I l f vol) {y : Box ι → F}
    (h : ∀ J ∈ π.boxes, HasIntegral J l f vol (y J)) :
    HasIntegral I l f vol (∑ J ∈ π.boxes, y J) := by
  have hsum : (∑ J ∈ π.boxes, y J) = integral I l f vol := by
    have hba := hI.toBoxAdditive.sum_partition_boxes le_rfl hπ
    simp only [Integrable.toBoxAdditive_apply] at hba
    rw [← hba]
    exact Finset.sum_congr rfl fun J hJ ↦ ((h J hJ).integral_eq).symm
  rw [hsum]
  exact hI.hasIntegral

/-- Two-box specialization of `HasIntegral.sum_of_isPartition`. -/
theorem HasIntegral.split [CompleteSpace F] (i : ι) (x : ℝ) {J_lo J_hi : Box ι}
    (h_lower : I.splitLower i x = ↑J_lo) (h_upper : I.splitUpper i x = ↑J_hi)
    {vol : ι →ᵇᵃ E →L[ℝ] F} (hI : Integrable I l f vol) {y_lo y_hi : F}
    (h₁ : HasIntegral J_lo l f vol y_lo) (h₂ : HasIntegral J_hi l f vol y_hi) :
    HasIntegral I l f vol (y_lo + y_hi) := by
  classical
  have : (I.splitLower i x  : Set (ι → ℝ)) ∩ (I.splitUpper i x  : Set (ι → ℝ)) = ∅ := by
    ext p; simp; grind
  have hne : J_hi ≠ J_lo := by
    intro heq
    simp [h_lower, h_upper, heq] at this
  let y : Box ι → F := fun J ↦ if J = J_lo then y_lo else y_hi
  have hy_lo : y J_lo = y_lo := if_pos rfl
  have hy_hi : y J_hi = y_hi := if_neg hne
  rw [← hy_lo, ← hy_hi]
  have h_sum_eq : (∑ J ∈ (Prepartition.split I i x).boxes, y J) = y J_lo + y J_hi := by
    rw [Prepartition.sum_split_boxes, h_lower, h_upper]
    rfl
  rw [← h_sum_eq]
  apply HasIntegral.sum_of_isPartition (Prepartition.isPartitionSplit I i x) hI
  intro J hJ
  rcases Prepartition.mem_split_iff.mp hJ with hJ | hJ
  · rw [WithBot.coe_injective (hJ.trans h_lower), hy_lo]; exact h₁
  · rw [WithBot.coe_injective (hJ.trans h_upper), hy_hi]; exact h₂

end BoxIntegral
