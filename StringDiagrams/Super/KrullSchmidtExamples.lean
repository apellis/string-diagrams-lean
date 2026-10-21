/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.KrullSchmidt
import StringDiagrams.Super.SKarUnit
import StringDiagrams.Super.UnitQPiEnvelope

/-!
# Concrete consumers of the integral Krull–Schmidt theorem

The rational unit superalgebra discharges the hypotheses of the finite-dimensional
K₀ results used in the BE2 §11 preliminary facts. Its rank-one even projective is
indecomposable and has nonzero class; the examples also exercise decomposition,
cancellation, the graded envelope, and the right-supermodule comparison.
-/

noncomputable section
namespace StringDiagrams.KrullSchmidtExamples
open CategoryTheory Limits Idempotents KrullSchmidt

/-- The rational algebra concentrated in integer degree zero and even parity. -/
def rationalGradedAlgebra : GradedSuperalgebra ℚ ℚ := by
  letI : SetLike.GradedMonoid (UnitSupercat.trivialDegree ℚ) :=
    { one_mem := by simp
      mul_mem := by
        intro m n a b ha hb
        rw [UnitSupercat.mem_trivialDegree_iff] at ha hb ⊢
        rcases ha with rfl | rfl
        · rcases hb with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (mul_zero _)
        · exact Or.inr (zero_mul _) }
  letI : GradedAlgebra (UnitSupercat.trivialDegree ℚ) :=
    { (inferInstance : SetLike.GradedMonoid (UnitSupercat.trivialDegree ℚ)),
      (UnitSupercat.isInternal_trivialDegree ℚ).chooseDecomposition with }
  exact
    { parity := trivialGrading ℚ
      degree := UnitSupercat.trivialDegree ℚ
      decompose_mem := by
        intro n a p ha
        rw [UnitSupercat.mem_trivialDegree_iff] at ha ⊢
        rcases ha with h | rfl
        · exact Or.inl h
        · right; simp }

example : Module.Free ℤ
    (K₀ (GSKar ℚ (SuperalgebraCat rationalGradedAlgebra.parity))) :=
  GSKarAlg.k0_free_int rationalGradedAlgebra

/-- Rank-one parity-shifted rational supermodules are indecomposable. -/
theorem isIndec_unitObj (a : ZMod 2) : IsIndec (SKarUnit.obj ℚ a) := by
  apply (isIndec_obj_iff (SKar.of ℚ (UnitSupercat ℚ)) (⟨⟨a, ()⟩⟩ : SKarUnit.D ℚ)).2
  constructor
  · intro h
    have h' := congrArg SKarUnit.scal ((IsZero.iff_id_eq_zero _).1 h)
    simp at h'
  · intro e he
    have he' : SKarUnit.scal e * SKarUnit.scal e = SKarUnit.scal e :=
      congrArg SKarUnit.scal he
    have h := mul_eq_zero.mp (show SKarUnit.scal e * (SKarUnit.scal e - 1) = 0 by
      rw [mul_sub, mul_one, he', sub_self])
    exact h.elim (fun h => Or.inl (SKarUnit.hom_ext h))
      (fun h => Or.inr (SKarUnit.hom_ext (sub_eq_zero.mp h)))

/-- The new theorem detects a nonzero class on explicit nonzero data. -/
theorem unitObj_class_ne_zero (a : ZMod 2) : K₀.mk (SKarUnit.obj ℚ a) ≠ 0 := by
  intro h
  have hp := multK_self_pos ℚ (isIndec_unitObj a)
  rw [h, map_zero] at hp
  exact (lt_irrefl 0) hp

/-- The abstract local-ring input is discharged on a rank-one projective. -/
example : IsLocalRing (End (SKarUnit.obj ℚ 0)) := (isIndec_unitObj 0).isLocalRing ℚ

example : Module.Free ℤ (K₀ (SKar ℚ (UnitSupercat ℚ))) :=
  SKarAlg.k0_free_int (trivialGrading ℚ)

example : Module.Free ℤ (K₀ (SKarAlg.FGProj (trivialGrading ℚ))) :=
  SKarAlg.fgProj_k0_free_int (trivialGrading ℚ)

example (P : SKarAlg.FGProj (trivialGrading ℚ)) :
    ∃ l : List (IndecClass (SKar ℚ (UnitSupercat ℚ))),
      Nonempty (P ≅ (SKarAlg.toFGProj (trivialGrading ℚ)).obj (sumList l)) :=
  SKarAlg.fgProj_exists_iso_sumList (trivialGrading ℚ) P

example (P : GSKar ℚ (UnitSupercat ℚ)) :
    ∃ l : List (IndecClass (GSKar ℚ (UnitSupercat ℚ))), Nonempty (P ≅ sumList l) :=
  exists_iso_sumList ℚ P

example : Module.Free ℤ (K₀ (GSKar ℚ (UnitSupercat ℚ))) :=
  KrullSchmidt.free ℚ

example (P Q : SKar ℚ (UnitSupercat ℚ)) : K₀.mk P = K₀.mk Q ↔ Nonempty (P ≅ Q) :=
  mk_eq_mk_iff ℚ

example (P Q Z : SKar ℚ (UnitSupercat ℚ)) (e : P ⊞ Z ≅ Q ⊞ Z) : Nonempty (P ≅ Q) :=
  cancel_biprod ℚ e

example (l m : List (IndecClass (SKar ℚ (UnitSupercat ℚ)))) :
    Nonempty (sumList l ≅ sumList m) ↔ l.Perm m := nonempty_iso_sumList_iff ℚ

#print axioms FiniteDimensionalAlgebra.isNilpotent_or_isUnit_of_idempotent
#print axioms KrullSchmidt.indecBasis
#print axioms KrullSchmidt.exists_iso_sumList
#print axioms KrullSchmidt.nonempty_iso_sumList_iff
#print axioms KrullSchmidt.mk_eq_mk_iff
#print axioms SKarAlg.fgProjIndecBasis
#print axioms SKarAlg.fgProj_exists_iso_sumList
#print axioms GSKarAlg.indecBasis
#print axioms unitObj_class_ne_zero

end StringDiagrams.KrullSchmidtExamples
