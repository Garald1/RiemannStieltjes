/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Basic

/-!
# Additions to `Mathlib.Analysis.BoxIntegral.Partition.Basic`

We define `BoxIntegral.Prepartition.mesh_size`, the largest sidelength of a box in a
prepartition; this is relevant for relating the box integral to the Riemann integral.
-/

@[expose] public section

open Set Finset Function
open scoped NNReal

noncomputable section

namespace BoxIntegral

variable {ι : Type*}

namespace Prepartition

section Mesh

variable [Fintype ι]

/-- The mesh size of a partition is the length of the longest side of a box in the partition. -/
noncomputable def mesh_size {I : Box ι} (π : Prepartition I) : NNReal :=
  (π.boxes ×ˢ (univ : Finset ι)).sup
  (fun ⟨ B, i ⟩ ↦ NNReal.mk (B.upper i - B.lower i) (by linarith [B.lower_lt_upper i]))

@[simp]
theorem mesh_size_le_iff {I : Box ι} (π : Prepartition I) (ε : NNReal) :
    π.mesh_size ≤ ε ↔ ∀ B ∈ π.boxes, ∀ i, B.upper i - B.lower i ≤ ε := by
  simp only [mesh_size, Finset.sup_le_iff, mem_product, mem_boxes,
    Prod.forall, tsub_le_iff_right, Finset.mem_univ, and_true]
  refine ⟨ fun h B hB i ↦ ?_, fun h B i hB ↦ (?_ : B.upper i - B.lower i ≤ ε) ⟩
  · have : B.upper i - B.lower i ≤ ε := h B i hB
    linarith
  · linarith [h B hB i]

end Mesh

end Prepartition

end BoxIntegral
