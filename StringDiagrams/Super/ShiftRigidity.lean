/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.QPiCategory
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic

/-!
# Integer-shift rigidity from a lower bound

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
§11, first preliminary fact used in Theorems 11.3 and 11.7.
A nonzero object whose graded endomorphisms are bounded below cannot be
isomorphic, by a degree-zero isomorphism, to a nontrivial integer shift.
Neither finite dimensionality nor indecomposability is needed for this step.
Degreewise finite dimensionality is separately needed for Krull–Schmidt.
-/

namespace StringDiagrams.GradedSupercategory
open CategoryTheory
variable {k C : Type*} [CommRing k] [Category C] [Preadditive C]
  [Linear k C] [Supercategory k C] [GradedSupercategory k C]

/-- The precise lower-bound hypothesis on the graded endomorphism space. -/
def EndBoundedBelow (X : C) : Prop :=
  ∃ N : ℤ, ∀ n < N, degree (R := k) X X n = ⊥

/-- Homogeneous powers have the expected degree. -/
theorem end_pow_mem_degree {X : C} {f : End X} {m : ℤ}
    (hf : f ∈ degree (R := k) X X m) (n : ℕ) :
    f ^ n ∈ degree (R := k) X X ((n : ℤ) * m) := by
  induction n with
  | zero => simpa using id_mem_degree (R := k) X
  | succ n ih =>
    simpa [pow_succ, End.mul_def, Nat.cast_add, Nat.cast_one, add_mul, add_comm]
      using comp_mem_degree hf ih

/-- A homogeneous automorphism of a nonzero bounded-below object has
nonnegative degree. Apply the same statement to its inverse to get degree zero. -/
theorem iso_degree_nonneg {X : C} (hX : ¬ Limits.IsZero X)
    (hB : EndBoundedBelow (k := k) X) (e : X ≅ X) {m : ℤ}
    (he : e.hom ∈ degree (R := k) X X m) : 0 ≤ m := by
  obtain ⟨N, hN⟩ := hB
  by_contra hm
  have hm' : m ≤ -1 := by omega
  let n : ℕ := N.natAbs + 1
  have hneg : -(n : ℤ) < N := by
    dsimp [n]
    have := Int.le_natAbs (a := -N)
    rw [Int.natAbs_neg] at this
    omega
  have hdeg : (n : ℤ) * m < N := by
    have := mul_le_mul_of_nonneg_left hm' (Int.natCast_nonneg n)
    nlinarith
  let f : End X := e.hom
  have hz : f ^ n = 0 := by
    have hp := end_pow_mem_degree (f := f) he n
    rw [hN _ hdeg] at hp
    exact hp
  have hu : IsUnit (f ^ n) :=
    ((isUnit_iff_isIso f).2 inferInstance).pow n
  obtain ⟨u, hu⟩ := hu
  have hid : (𝟙 X : X ⟶ X) = 0 := by
    have h := u.val_inv
    rw [hu, hz, zero_mul] at h
    exact h.symm
  exact hX ((Limits.IsZero.iff_id_eq_zero X).2 hid)

/-- Homogeneous automorphisms of nonzero bounded-below objects have degree zero. -/
theorem iso_degree_eq_zero {X : C} (hX : ¬ Limits.IsZero X)
    (hB : EndBoundedBelow (k := k) X) (e : X ≅ X) {m : ℤ}
    (he : e.hom ∈ degree (R := k) X X m) : m = 0 := by
  have h := iso_degree_nonneg hX hB e he
  have h' := iso_degree_nonneg hX hB e.symm (inv_mem_degree e he)
  omega

/-- Integer-shift rigidity. The isomorphism is explicitly degree zero;
the ungraded shift isomorphism `σPow` is not such an isomorphism. -/
theorem qPow_iso_degree_zero {X : C} [QPiSupercategory k C]
    (hX : ¬ Limits.IsZero X) (hB : EndBoundedBelow (k := k) X)
    (m : ℤ) (e : QPiSupercategory.qPow k m X ≅ X)
    (he : e.hom ∈ degree (R := k) _ X 0) : m = 0 := by
  let f := (QPiSupercategory.σPow k m X).symm ≪≫ e
  apply iso_degree_eq_zero hX hB f
  simpa only [f, Iso.trans_hom, Iso.symm_hom, add_zero] using comp_mem_degree
    (QPiSupercategory.σPow_inv_mem_degree (R := k) m X) he

end StringDiagrams.GradedSupercategory
