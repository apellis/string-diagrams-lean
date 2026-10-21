/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.GSKarLaurent
import StringDiagrams.Super.ShiftRigidity
import StringDiagrams.Super.UnitQPiEnvelope
import StringDiagrams.Super.KrullSchmidtExamples

/-!
# Nonzero Laurent Krull–Schmidt examples

The rational field concentrated in degree zero exercises the Laurentian
hypotheses, the integer-shift orbit basis and the nonzero rank-one projective
in the corrected BE2 §11 preliminary fact used by Theorems 11.3 and 11.7.
-/

noncomputable section
namespace StringDiagrams.KrullSchmidtLaurentExamples
open CategoryTheory Limits Idempotents KrullSchmidt GradedSupercategory

instance : GSKar.DegreeHomFinite (k := ℚ) (C := UnitSupercat ℚ) where
  finiteDimensional X Y n := by
    change FiniteDimensional ℚ (UnitSupercat.trivialDegree ℚ n)
    infer_instance

/-- The rational field satisfies the required lower bound, not an assumed rigidity axiom. -/
theorem rational_bound : GSKar.HomBoundedBelow (k := ℚ) (C := UnitSupercat ℚ) := by
  intro X Y
  exact ⟨0, fun n hn => UnitSupercat.trivialDegree_of_ne ℚ (by omega)⟩

/-- The completed category's Laurent freeness follows from the degreewise hypotheses. -/
theorem rational_k0_free :
    letI := K₀.moduleLaurentInt ℚ (GSKar ℚ (UnitSupercat ℚ))
    Module.Free (LaurentPolynomial ℤ) (K₀ (GSKar ℚ (UnitSupercat ℚ))) :=
  GSKar.k0_free_laurentInt rational_bound

/-- The explicit orbit basis, with all shift bounds discharged. -/
def rational_basis := KrullSchmidt.laurentBasis ℚ (GSKar.shiftHomBoundedBelow rational_bound)

/-- The degree-zero even line before completion. -/
def point : GSKar.ShiftBase ℚ (UnitSupercat ℚ) := ⟨⟨UnitQPiEnvelope.P ℚ 0 0⟩⟩

/-- The fully faithful embedding into the graded additive Karoubi envelope. -/
def embed : GSKar.ShiftBase ℚ (UnitSupercat ℚ) ⥤ GSKar ℚ (UnitSupercat ℚ) :=
  Mat_.embedding _ ⋙ toKaroubi _

instance : embed.Full := inferInstanceAs (Mat_.embedding _ ⋙ toKaroubi _).Full
instance : embed.Faithful := inferInstanceAs (Mat_.embedding _ ⋙ toKaroubi _).Faithful
instance : embed.Additive := inferInstanceAs (Mat_.embedding _ ⋙ toKaroubi _).Additive

/-- The rank-one graded projective. -/
def line : GSKar ℚ (UnitSupercat ℚ) := embed.obj point

/-- The rank-one line is indecomposable, with even degree-zero endomorphism ring ℚ. -/
theorem line_indec : IsIndec line := by
  apply (isIndec_obj_iff embed point).2
  constructor
  · intro h
    have hz := congrArg (fun f : point ⟶ point => (f.val.val : ℚ))
      ((IsZero.iff_id_eq_zero point).1 h)
    exact (one_ne_zero : (1 : ℚ) ≠ 0) hz
  · intro f hf
    let a : ℚ := f.val.val
    have ha : a * a = a := congrArg (fun f : point ⟶ point => (f.val.val : ℚ)) hf
    have h := mul_eq_zero.mp (show a * (a - 1) = 0 by rw [mul_sub, mul_one, ha, sub_self])
    rcases h with h | h
    · left; apply Subtype.ext; apply Subtype.ext; exact h
    · right; apply Subtype.ext; apply Subtype.ext; exact sub_eq_zero.mp h

/-- The example's Grothendieck group is nonzero. -/
theorem line_class_ne_zero : K₀.mk line ≠ 0 := by
  intro h
  have hp := multK_self_pos ℚ line_indec
  rw [h, map_zero] at hp
  exact (lt_irrefl 0) hp

/-- The indecomposable line has no nontrivial integer period. -/
theorem line_shift_rigid (n : ℤ)
    (h : indecShift ℚ n (Quotient.mk (indecSetoid _) ⟨line, line_indec⟩) =
      Quotient.mk (indecSetoid _) ⟨line, line_indec⟩) : n = 0 :=
  indec_shift_free ℚ (GSKar.shiftHomBoundedBelow rational_bound) _ n h

/-- The homogeneous-automorphism rigidity theorem on a concrete nonzero object. -/
example (e : (UnitQPiEnvelope.P ℚ 0 0) ≅ UnitQPiEnvelope.P ℚ 0 0) (n : ℤ)
    (he : e.hom ∈ degree (R := ℚ) _ _ n) : n = 0 := by
  apply iso_degree_eq_zero (X := UnitQPiEnvelope.P ℚ 0 0) _ _ e he
  · intro h
    have hz := (IsZero.iff_id_eq_zero _).1 h
    exact one_ne_zero (show (1 : ℚ) = 0 from hz)
  · refine ⟨0, fun m hm => ?_⟩
    change UnitSupercat.trivialDegree ℚ (m + (0 - 0)) = ⊥
    simpa using UnitSupercat.trivialDegree_of_ne ℚ (n := m) (by omega)

/-- The superalgebra consumer on the rational graded field. -/
example :
    letI := K₀.moduleLaurentInt ℚ
      (GSKar ℚ (SuperalgebraCat KrullSchmidtExamples.rationalGradedAlgebra.parity))
    Module.Free (LaurentPolynomial ℤ)
      (K₀ (GSKar ℚ (SuperalgebraCat KrullSchmidtExamples.rationalGradedAlgebra.parity))) :=
  GSKarAlg.k0_free_laurentInt KrullSchmidtExamples.rationalGradedAlgebra
    (fun _ => inferInstance) ⟨0, fun _ hn => UnitSupercat.trivialDegree_of_ne ℚ (by omega)⟩

#print axioms GSKarAlg.k0_free_laurentInt
#print axioms KrullSchmidt.laurentBasis
#print axioms KrullSchmidt.k0_free_laurentInt
#print axioms GSKar.k0_free_laurentInt
#print axioms GradedSupercategory.qPow_iso_degree_zero
#print axioms rational_k0_free
#print axioms line_class_ne_zero

end StringDiagrams.KrullSchmidtLaurentExamples
