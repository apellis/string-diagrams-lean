/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.KrullSchmidtLaurent
import StringDiagrams.Super.KrullSchmidtParity
import StringDiagrams.Super.LaurentParityOrbits
import StringDiagrams.Super.LaurentParityDecomposition

/-!
# The mixed Laurent Krull–Schmidt decomposition

The corrected first preliminary fact of BE2 §11, used in Theorems 11.3 and 11.7.
The integral basis and Laurentian lower bound yield a parity-compatible Laurent
basis and hence the ℒ-module decomposition into type-M free summands and type-Q
quotients by π − 1. Parity-fixed indecomposables are retained.
-/

noncomputable section
namespace StringDiagrams.KrullSchmidt
open CategoryTheory Limits Idempotents Module LaurentPolynomial
variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C]
  [Linear k C] [QPiCategory k C] [HasBinaryBiproducts C]
  [HomFinite k C] [IsIdempotentComplete C]

/-- Parity acts on the integral indecomposable basis through the covering Laurent action. -/
theorem covering_pi_smul_indec (i : IndecClass C) :
    letI := K₀.moduleLaurent k C
    CoveringLaurent.pi • indecBasis k i = indecBasis k (indecParity k i) := by
  let := K₀.moduleLaurent k C
  simp only [indecBasis_apply]
  rw [CoveringLaurent.pi, K₀.C_π_smul_mk]
  exact K₀.mk_eq_mk_of_iso (indecParity_rep_iso k i).some

/-- Integer monomials act on the same integral basis through the covering action. -/
theorem covering_T_smul_indec (n : ℤ) (i : IndecClass C) :
    letI := K₀.moduleLaurent k C
    (T n : LaurentPolynomial Zπ) • indecBasis k i = indecBasis k (indecShift k n i) := by
  let := K₀.moduleLaurent k C
  have h := int_T_smul_indec k n i
  change CoveringLaurent.inclusion (T n : LaurentPolynomial ℤ) • K₀.mk i.rep =
    K₀.mk (indecShift k n i).rep at h
  simpa only [CoveringLaurent.inclusion, T, AddMonoidAlgebra.mapRingHom_single,
    map_one, indecBasis_apply] using h

/-- Parity and every integer shift commute on indecomposable classes. -/
theorem indecParity_shift (n : ℤ) (i : IndecClass C) :
    indecParity k (indecShift k n i) = indecShift k n (indecParity k i) := by
  let := K₀.moduleLaurent k C
  apply (indecBasis k).injective
  rw [← covering_pi_smul_indec, ← covering_T_smul_indec,
    ← covering_T_smul_indec, ← covering_pi_smul_indec]
  rw [← mul_smul, mul_comm CoveringLaurent.pi (T n : LaurentPolynomial Zπ), mul_smul]

/-- Indecomposable isomorphism classes modulo integer grading shifts. -/
abbrev ShiftOrbit := @Quotient (IndecClass C) (@AddAction.orbitRel ℤ _ _ (indecShiftAction k))

/-- Parity on the integer-shift orbit set. -/
def laurentParity : ShiftOrbit k (C := C) → ShiftOrbit k (C := C) := by
  letI := indecShiftAction k (C := C)
  exact LaurentBasis.orbitParity (indecParity k) (indecParity_shift k)

/-- The induced parity action is involutive. -/
theorem laurentParity_involutive : Function.Involutive (laurentParity k (C := C)) := by
  let := indecShiftAction k (C := C)
  exact LaurentBasis.orbitParity_involutive _ (indecParity_involutive k) (indecParity_shift k)

/-- An arbitrary order is used only to choose between paired orbits. -/
@[instance_reducible] def laurentOrbitOrder : LinearOrder (ShiftOrbit k (C := C)) := by
  classical
  exact linearOrderOfSTO (WellOrderingRel : ShiftOrbit k (C := C) → _ → Prop)

/-- Normalize the Laurent basis so that parity permutes it without powers of q. -/
def parityLaurentBasis (h : ShiftHomBoundedBelow k (C := C)) :
    letI := K₀.moduleLaurentInt k C
    Basis (ShiftOrbit k (C := C)) (LaurentPolynomial ℤ) (K₀ C) := by
  letI := K₀.moduleLaurentInt k C
  letI := indecShiftAction k (C := C)
  letI := laurentOrbitOrder k (C := C)
  exact LaurentBasis.parityCompatibleBasis (indecParity k) (indecParity_involutive k)
    (indecParity_shift k) (indec_shift_free k h) (indecBasis k)
    (fun n i => by
      simp only [indecBasis_apply]
      exact int_T_smul_indec k n i)

/-- Compatibility with the already selected covering-Laurent action. -/
theorem parityLaurentBasis_pi (h : ShiftHomBoundedBelow k (C := C))
    (o : ShiftOrbit k (C := C)) :
    letI := K₀.moduleLaurent k C
    CoveringLaurent.pi • parityLaurentBasis k h o =
      parityLaurentBasis k h (laurentParity k o) := by
  let := K₀.moduleLaurent k C
  let := K₀.moduleLaurentInt k C
  let := indecShiftAction k (C := C)
  let := laurentOrbitOrder k (C := C)
  exact LaurentBasis.parityCompatibleBasis_parity (indecParity k) (indecParity_involutive k)
    (indecParity_shift k) (indec_shift_free k h) (indecBasis k)
    (fun n i => by
      simp only [indecBasis_apply]
      exact int_T_smul_indec k n i)
    (fun x => CoveringLaurent.pi • x) (covering_pi_smul_indec k) o

/-- The corrected ℒ-linear direct-sum decomposition on the existing split K₀. -/
def laurentDecomposition (h : ShiftHomBoundedBelow k (C := C)) :=
  letI := K₀.moduleLaurent k C
  letI := K₀.moduleLaurentInt k C
  letI := laurentOrbitOrder k (C := C)
  CoveringLaurent.quotientDecomposition (parityLaurentBasis k h) (laurentParity k)
    (laurentParity_involutive k) (parityLaurentBasis_pi k h)

/-- Fixed grading-shift orbits are exactly parity-self-associate indecomposables;
there is no hidden nonzero grading twist. -/
theorem laurentParity_fixed_iff (h : ShiftHomBoundedBelow k (C := C)) (i : IndecClass C) :
    laurentParity k (Quotient.mk _ i) = Quotient.mk _ i ↔
      Nonempty ((PiCategory.pi (R := k)).obj i.rep ≅ i.rep) := by
  let := indecShiftAction k (C := C)
  exact (LaurentBasis.orbitParity_fixed_iff (indecParity k) (indecParity_involutive k)
    (indecParity_shift k) (indec_shift_free k h) i).trans (indecParity_eq_iff k i)

#print axioms laurentDecomposition
#print axioms laurentParity_fixed_iff

end StringDiagrams.KrullSchmidt
