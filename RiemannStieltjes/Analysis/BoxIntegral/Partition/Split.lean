/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Split
public import RiemannStieltjes.Analysis.BoxIntegral.Partition.Basic

/-!
# Additions to `Mathlib.Analysis.BoxIntegral.Partition.Split`
-/

@[expose] public section

noncomputable section

open Function Set Filter

namespace BoxIntegral

variable {ι M : Type*} {n : ℕ}

namespace Box

/-- The lower corner of `splitLower I i x` (when it is nonempty) coincides with the lower
corner of `I`. -/
theorem splitLower_unbot_lower {I : Box ι} {i : ι} {x : ℝ}
    (h : I.splitLower i x ≠ ⊥) :
    ((I.splitLower i x).unbot h).lower = I.lower := by
  have h_coe := WithBot.coe_unbot (I.splitLower i x) h
  unfold splitLower at h_coe
  exact (mk'_eq_coe.mp h_coe.symm).1.symm

/-- The upper corner of `splitLower I i x` (when it is nonempty), evaluated at the split
coordinate `i`, equals `min x (I.upper i)`. -/
theorem splitLower_unbot_upper_apply_self {I : Box ι} {i : ι} {x : ℝ}
    (h : I.splitLower i x ≠ ⊥) :
    ((I.splitLower i x).unbot h).upper i = min x (I.upper i) := by
  classical
  have h_coe : (((I.splitLower i x).unbot h : Box ι) : WithBot (Box ι)) =
      mk' I.lower (update I.upper i (min x (I.upper i))) := WithBot.coe_unbot _ h
  have := congrArg (· i) (mk'_eq_coe.mp h_coe.symm).2.symm
  simpa using this

end Box

namespace Prepartition

variable {I J : Box ι} {i : ι} {x : ℝ}

/-- Distinct boxes of a prepartition map to disjoint `splitLower`s. Combined with non-bot-ness on
one side, this says `splitLower (· i x)` is injective on those boxes of the prepartition whose
splits are nonempty. -/
theorem splitLower_injOn {π : Prepartition I} {J1 J2 : Box ι}
    (hJ1 : J1 ∈ π.boxes) (hJ2 : J2 ∈ π.boxes)
    (hne_bot : J1.splitLower i x ≠ ⊥)
    (h_eq : J1.splitLower i x = J2.splitLower i x) : J1 = J2 := by
  by_contra hne
  have hdisj : Disjoint (J1.splitLower i x) (J2.splitLower i x) := by
    rw [← Box.disjoint_withBotCoe, Box.coe_splitLower, Box.coe_splitLower]
    exact (π.disjoint_coe_of_mem hJ1 hJ2 hne).mono
      Set.inter_subset_left Set.inter_subset_left
  rw [h_eq, disjoint_self] at hdisj
  exact (h_eq ▸ hne_bot) hdisj

end Prepartition

end BoxIntegral
