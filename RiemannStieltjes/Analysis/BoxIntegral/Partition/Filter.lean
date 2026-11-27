/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Filter
public import RiemannStieltjes.Analysis.BoxIntegral.Partition.Split

import Mathlib.Tactic.Peel

/-!
# Additions to `Mathlib.Analysis.BoxIntegral.Partition.Filter`

API for simplifying the filters in `BoxIntegral`, especially in the case of Riemann integration
parameters.
-/

@[expose] public section

namespace NNReal

/-! ## Nonnegative real API
To be upstreamed to NNReal?
-/

@[simp]
lemma coe_sup_le_iff_forall_le {β : Type*} {s : Finset β} {f : β → NNReal} {R : ℝ} (hR : 0 ≤ R) :
    ↑(s.sup f) ≤ R ↔ ∀ b ∈ s, ↑(f b) ≤ R := by
  rw [←coe_mk R hR]
  simp only [Finset.sup_le_iff, coe_le_coe]

end NNReal


open Set Function Filter Metric Finset Bool
open scoped Topology Filter NNReal

noncomputable section

namespace BoxIntegral

namespace IntegrationParams

section Riemann

/-! ### Simplifying the BoxIntegral filters

API for simplifying the filters in `BoxIntegral`, especially in the case of Riemann integration
parameters.  We will focus here on simplifying `toFilteriUnion`, as this is the main filter used
to define box integration.

-/

open Prepartition TaggedPrepartition Finset NNReal

variable {ι : Type*} [Fintype ι] (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)

theorem toFilteriUnion_eventually_iff (P : TaggedPrepartition I → Prop) :
    (∀ᶠ π in l.toFilteriUnion I π₀, P π) ↔ ∃ (r : NNReal → _),
    (∀ c, l.RCond (r c)) ∧
    ∀ π, (∃ c, l.MemBaseSet I c (r c) π ∧ π.iUnion = π₀.iUnion) → P π
     := by
  simp [(l.hasBasis_toFilteriUnion I π₀).eventually_iff]

@[simp]
lemma Riemann_bRiemann_true : Riemann.bRiemann = true := rfl

@[simp]
lemma Riemann_bHenstock_true : Riemann.bHenstock = true := rfl

@[simp]
lemma Riemann_bDistortion_false : Riemann.bDistortion = false := rfl

theorem Riemann_toFilteriUnion_eventually_iff (P : TaggedPrepartition I → Prop) :
    (∀ᶠ π in Riemann.toFilteriUnion I π₀, P π) ↔ ∃ (r : Set.Ioi 0),
    ∀ π, (π.IsSubordinate (fun _ ↦ r) ∧ π.IsHenstock ∧ π.iUnion = π₀.iUnion) → P π
     := by
  simp only [toFilteriUnion_eventually_iff, exists_and_right, and_imp, forall_exists_index,
    Subtype.exists, Set.mem_Ioi]
  refine ⟨ fun ⟨ r, hr, hr' ⟩ ↦ ⟨ r 1 0, by grind, ?_ ⟩,
    fun ⟨ r, hpos, hr ⟩ ↦ ⟨ fun _ _ ↦ ⟨ r, hpos ⟩, fun c ↦ by simp [RCond], fun π c hmem ↦ ?_ ⟩ ⟩
  · simp only [Subtype.coe_eta]
    peel hr' with π h
    refine fun hsub hhen ↦ h 1 ⟨ ?_, by simp [hhen], by simp, by simp ⟩
    convert hsub using 2 with x
    apply hr 1; simp
  apply hr π hmem.isSubordinate (hmem.isHenstock (by simp))

/-- A statement is eventually true under the Riemann filter if it is true for all tagged (Henstock)
partitions with sufficiently small mesh size. -/
theorem Riemann_toFilteriUnion_eventually_iff_mesh (P : TaggedPrepartition I → Prop) :
    (∀ᶠ π in Riemann.toFilteriUnion I π₀, P π) ↔ ∃ ε > 0,
    ∀ π, (↑π.mesh_size ≤ ε ∧ π.IsHenstock ∧ π.iUnion = π₀.iUnion) → P π
     := by
  simp only [Riemann_toFilteriUnion_eventually_iff, IsSubordinate, Box.Icc_def, IsHenstock,
    Set.mem_Icc, and_imp, Subtype.exists, Set.mem_Ioi, exists_prop, gt_iff_lt]
  refine ⟨ fun ⟨ r, hpos, hr ⟩ ↦ ⟨ NNReal.mk r (le_of_lt hpos), hpos, ?_ ⟩,
    fun ⟨ ε, (εpos : 0 < ε), hε ⟩ ↦ ⟨ (ε/2 : NNReal), by positivity, ?_ ⟩ ⟩
  · replace hpos := le_of_lt hpos
    peel hr with π h
    refine fun hmesh hhen hunion ↦ h ?_ hhen hunion
    intro J hJ x hx
    simp only [Metric.mem_closedBall, dist_pi_def, hpos, coe_sup_le_iff_forall_le,
      coe_nndist]
    intro i
    simp only [Set.mem_Icc, π.mesh_size_le_iff, Pi.le_def]
      at hx hmesh hhen ⊢
    have : J.upper i - J.lower i ≤ r := hmesh J hJ i
    specialize hhen J (by simp [hJ])
    grind [Real.dist_eq, abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right]
  peel hε with π h
  refine fun hsub hhen hunion ↦ h ?_ hhen hunion
  simp only [π.mesh_size_le_iff]
    at hsub hhen ⊢
  rintro J hJi i
  simp only [mem_boxes, mem_toPrepartition, tsub_le_iff_right] at hJi ⊢
  have hsub1 := hsub J hJi J.lower_mem_Icc
  have hsub2 := hsub J hJi J.upper_mem_Icc
  specialize hhen J hJi
  simp only [Pi.le_def, Metric.mem_closedBall, dist_pi_def,
    NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ, forall_const] at hhen hsub1 hsub2
  replace hsub1 : dist (J.lower i) (π.tag J i) ≤ (ε/2 : NNReal) := hsub1 i
  replace hsub2 : dist (J.upper i) (π.tag J i) ≤ (ε/2 : NNReal) := hsub2 i
  simp at hsub1 hsub2
  grind [Real.dist_eq, abs_le, NNReal.coe_div]

end Riemann

end IntegrationParams

end BoxIntegral
