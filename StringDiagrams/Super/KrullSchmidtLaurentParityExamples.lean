/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.GSKarLaurentParity
import StringDiagrams.Super.KrullSchmidtLaurentExamples

/-!
# Nonzero consumers of the mixed Laurent decomposition

The rational graded field supplies the categorical and superalgebra consumers
for the corrected BE2 §11 preliminary fact. The parity-fixed coefficient
summand is separately proved nonzero, so it cannot be silently discarded.
-/

noncomputable section
namespace StringDiagrams.KrullSchmidtLaurentParityExamples
open KrullSchmidtLaurentExamples

/-- A categorical decomposition with all Laurentian hypotheses discharged. -/
def rational_decomposition := GSKar.laurentDecomposition rational_bound

/-- The decomposition retains the nonzero rank-one projective class. -/
theorem rational_coordinates_ne_zero :
    rational_decomposition.symm (K₀.mk line) ≠ 0 := by
  intro h
  have hh := congrArg rational_decomposition h
  exact line_class_ne_zero (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using hh)

/-- The graded-superalgebra statement specializes to the rational field. -/
def rational_algebra_decomposition :=
  GSKarAlg.laurentDecomposition KrullSchmidtExamples.rationalGradedAlgebra
    (fun _ => inferInstance) ⟨0, fun _ hn => UnitSupercat.trivialDegree_of_ne ℚ (by omega)⟩

/-- The type-Q quotient coefficient has a nonzero unit. -/
theorem typeQ_unit_ne_zero :
    (1 : CoveringLaurent.S ⧸ Ideal.span ({CoveringLaurent.pi - 1} : Set CoveringLaurent.S)) ≠ 0 := by
  intro h
  have hh := congrArg CoveringLaurent.quotientEval h
  exact (one_ne_zero : (1 : CoveringLaurent.R) ≠ 0) (by simpa only [map_one, map_zero] using hh)

/-- The parity-fixed quotient is an ℒ-module, not a claim of ℒ-freeness. -/
example := CoveringLaurent.typeQEquiv

#print axioms KrullSchmidt.laurentDecomposition
#print axioms GSKarAlg.laurentDecomposition
#print axioms rational_coordinates_ne_zero
#print axioms typeQ_unit_ne_zero

end StringDiagrams.KrullSchmidtLaurentParityExamples
