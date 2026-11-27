/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Additive
public import RiemannStieltjes.Analysis.BoxIntegral.Partition.Split
public import RiemannStieltjes.Analysis.BoxIntegral.Box.Ioc

/-!
# Additions to `Mathlib.Analysis.BoxIntegral.Partition.Additive`

In one dimension, we associate a box additive map `ofDiff g` to a function `g : ℝ → M` by the
formula `ofDiff g (Ioc a b) = g b - g a`.  This is used to define the Riemann–Stieltjes integral
in `BoxIntegral.Stieltjes`.
-/

@[expose] public section

noncomputable section

open Function Set

namespace BoxIntegral

variable {ι M : Type*} {n : ℕ}

namespace BoxAdditiveMap

open Box Prepartition Finset

variable {N : Type*} [AddCommMonoid M] [AddCommMonoid N] {I₀ : WithTop (Box ι)} {I : Box ι}
  {i : ι}

@[ext]
theorem ext_funLike {ι M : Type*} [AddCommMonoid M] {I₀ : WithTop (Box ι)}
    {f g : ι →ᵇᵃ[I₀] M} (h : ∀ J, f J = g J) : f = g :=
  DFunLike.ext _ _ h


@[simp]
lemma add_apply {ι M : Type*} [AddCommMonoid M] {I₀ : WithTop (Box ι)}
    (f g : ι →ᵇᵃ[I₀] M) (J : Box ι) : (f + g) J = f J + g J := rfl

@[simp]
lemma smul_apply {ι M : Type*} [AddCommMonoid M] {I₀ : WithTop (Box ι)}
    {R : Type*} [Monoid R] [DistribMulAction R M]
    (c : R) (f : ι →ᵇᵃ[I₀] M) (J : Box ι) : (c • f) J = c • (f J) := rfl

section AddCommGroup

/-! ### Additive group structure -/

variable {M : Type*} [AddCommGroup M]

instance {ι : Type*} {I₀ : WithTop (Box ι)} : Neg (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f ↦
    ⟨-(f : Box ι → M), fun I hI π hπ ↦ by
      simp only [Pi.neg_apply, Finset.sum_neg_distrib, sum_partition_boxes _ hI hπ]⟩⟩

instance {ι : Type*} {I₀ : WithTop (Box ι)} : Sub (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f g ↦
    ⟨(f : Box ι → M) - g, fun I hI π hπ ↦ by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_partition_boxes _ hI hπ]⟩⟩

instance {ι : Type*} {I₀ : WithTop (Box ι)} : AddCommGroup (ι →ᵇᵃ[I₀] M) :=
  Function.Injective.addCommGroup _ DFunLike.coe_injective
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp]
lemma neg_apply {ι : Type*} {I₀ : WithTop (Box ι)} (f : ι →ᵇᵃ[I₀] M) (J : Box ι) :
    (-f) J = -(f J) := rfl

@[simp]
lemma sub_apply {ι : Type*} {I₀ : WithTop (Box ι)} (f g : ι →ᵇᵃ[I₀] M) (J : Box ι) :
    (f - g) J = f J - g J := rfl

/-! ## The differential `ofDiff` of a function on `ℝ` -/

/-- Underlying construction for `ofDiff`: sends `g : ℝ → M` to the box-additive map on
`Box (Fin 1)` defined by `J ↦ g J.upper₁ - g J.lower₁`. -/
def ofDiffAux (g : ℝ → M) : (Fin 1) →ᵇᵃ M :=
  ofMapSplitAdd (fun J : Box (Fin 1) ↦ g J.upper₁ - g J.lower₁) ⊤
    (fun I _ i x hx ↦ by
      fin_cases i
      rw [splitLower_def hx, splitUpper_def hx]
      simp [Option.elim', upper₁, lower₁])

@[simp]
private lemma ofDiffAux_apply (g : ℝ → M) (J : Box (Fin 1)) :
    ofDiffAux g J = g J.upper₁ - g J.lower₁ := rfl

/-- The box-additive "differential" sending a function `g : ℝ → M` to the box-additive map on
`Box (Fin 1)` defined by `J ↦ g J.upper₁ - g J.lower₁`, bundled as an
`AddMonoidHom`. -/
def ofDiff : (ℝ → M) →+ ((Fin 1) →ᵇᵃ M) where
  toFun := ofDiffAux
  map_zero' := by ext; simp
  map_add' g h := by ext; simp [sub_add_sub_comm]

@[simp]
lemma ofDiff_apply (g : ℝ → M) (J : Box (Fin 1)) :
    ofDiff g J = g J.upper₁ - g J.lower₁ := rfl

@[simp]
lemma ofDiff_smul {R : Type*} [Monoid R] [DistribMulAction R M] (c : R) (g : ℝ → M) :
    ofDiff (c • g) = c • ofDiff g := by ext J; simp [smul_sub]

/-- The differential of a constant function vanishes. -/
@[simp]
lemma ofDiff_const (c : M) : ofDiff (fun _ : ℝ ↦ c) = 0 := by ext; simp

lemma ofDiff_id : ofDiff id = Box.len := rfl

@[simp]
lemma ofDiff_Ioc (g : ℝ → M) {a b : ℝ} (h : a < b) : ofDiff g (Ioc a b) = g b - g a := by simp [h]

/-- `ofDiff g` vanishes iff `g` is constant. -/
lemma ofDiff_eq_zero_iff {g : ℝ → M} : ofDiff g = 0 ↔ ∀ x y, g x = g y := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ by ext J; simp [h J.upper₁ J.lower₁]⟩
  have key : ∀ {a b : ℝ}, a < b → g b = g a := fun {a b} hab ↦
    sub_eq_zero.mp (by simpa [hab] using DFunLike.congr_fun h (Ioc a b))
  rcases lt_trichotomy x y with hxy | rfl | hxy
  exacts [(key hxy).symm, rfl, key hxy]

/-- `ofDiff` commutes with `BoxAdditiveMap.map` along an `AddMonoidHom`: postcomposing the
differential `ofDiff g` by `φ : M →+ N` is the same as taking the differential of `φ ∘ g`. -/
@[simp]
lemma map_ofDiff {N : Type*} [AddCommGroup N] (g : ℝ → M) (φ : M →+ N) :
    (ofDiff g).map φ = ofDiff (φ ∘ g) := by ext J; simp [map_sub]

/-- Telescoping series for one-dimensional box partitions. -/
lemma _root_.BoxIntegral.Prepartition.IsPartition.sum_of_sub {I : Box (Fin 1)}
    {π : Prepartition I} (hπ : π.IsPartition) (f : ℝ → M)
    : ∑ J ∈ π.boxes, (f J.upper₁ - f J.lower₁) = f I.upper₁ - f I.lower₁ :=
  (ofDiff f).sum_partition_boxes (by simp) hπ

/-- Additivity of length. -/
@[simp]
lemma _root_.BoxIntegral.Prepartition.IsPartition.sum_of_len {I : Box (Fin 1)}
    {π : Prepartition I} (hπ : π.IsPartition) : ∑ J ∈ π.boxes, J.len = I.len := by
  simpa [←ofDiff_id] using hπ.sum_of_sub id

end AddCommGroup

end BoxAdditiveMap

end BoxIntegral
