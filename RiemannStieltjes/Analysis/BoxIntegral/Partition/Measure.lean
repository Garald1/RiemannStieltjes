/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Measure
public import RiemannStieltjes.Analysis.BoxIntegral.Partition.Additive

/-!
# Additions to `Mathlib.Analysis.BoxIntegral.Partition.Measure`
-/

@[expose] public section

open Set

noncomputable section

open scoped ENNReal BoxIntegral

variable {ι : Type*}

namespace BoxIntegral

open MeasureTheory

namespace BoxAdditiveMap

/-- The Riemann–Stieltjes differential of `ContinuousLinearMap.lsmul ℝ ℝ : ℝ → (E →L[ℝ] E)`
equals the Lebesgue volume box-additive map on `Box (Fin 1)`. -/
lemma ofDiff_lsmul_eq_volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ofDiff (fun x : ℝ ↦ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) x) =
      (BoxAdditiveMap.volume : (Fin 1) →ᵇᵃ E →L[ℝ] E) := by
  ext
  simp [volume_apply, Box.upper₁, Box.lower₁]
  module

end BoxAdditiveMap

end BoxIntegral
