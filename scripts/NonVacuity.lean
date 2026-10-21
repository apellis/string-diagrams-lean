import StringDiagrams

/-!
# Non-vacuity checks for the headline theorems

Each `example` below applies a headline theorem to a concrete datum and discharges every
hypothesis by proof. If a later change makes a hypothesis set unsatisfiable for these data, or
breaks the statement's shape, this file stops compiling and CI fails. Where cheap, a second
`example` records that the conclusion is not degenerate.

Data: the ground ring `ℤ` for Brundan–Ellis Theorems 5.3 and 6.13 and Corollary 5.6 (whose only
hypothesis is a commutative ring); `ℚ` with `q = 2` (not a root of unity) for the odd
Temperley–Lieb appendix; `ℚ` for the Temperley–Lieb representation.
-/

open CategoryTheory

noncomputable section

namespace NonVacuity

/-! ### Brundan–Ellis, Theorem 5.3, Corollary 5.6, Theorem 6.13 -/

example := StringDiagrams.PiCat.theorem53.{0, 0, 0} ℤ

example := StringDiagrams.PiCat.twoSuperequivalent_piSCat_associated2.{0, 0, 0} (R := ℤ)

example := StringDiagrams.QPiCat.theorem613.{0, 0, 0} ℤ

/-! ### Odd Temperley–Lieb, Theorems A.2 and A.3, at `q = 2` over `ℚ` -/

section OddTL

open StringDiagrams.OddTemperleyLieb

/-- `q = 2` in `ℚˣ`. -/
def q2 : ℚˣ := Units.mk0 2 two_ne_zero

theorem hq2 : ∀ n : ℕ, 0 < n → q2 ^ n ≠ 1 := by
  intro n hn h
  have h' : (2 : ℚ) ^ n = 1 := by simpa [q2] using congrArg Units.val h
  exact (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) hn.ne').ne' h'

theorem hchar : ringChar ℚ ≠ 2 := by simp

example (m n : ℕ) := theoremA2 hchar q2 hq2 (isRepresentatives_repDiagram m n)

example (n : ℕ) (a : ZMod 2) := simple_jwObj q2 hq2 n a

example := basisK₀ q2 hq2

/-- Non-degeneracy: two different `P n a` are not isomorphic. -/
example : IsEmpty (jwObj q2 hq2 0 0 ≅ jwObj q2 hq2 1 0) :=
  isEmpty_iso_jwObj q2 hq2 (Or.inl zero_ne_one)

end OddTL

/-! ### Temperley–Lieb representation over `ℚ` -/

example := StringDiagrams.TemperleyLieb.Rep.respects ℚ

/-- Non-degeneracy: the image of a generator is nonzero. -/
example := StringDiagrams.TemperleyLieb.Rep.e_ne_zero (R := ℚ) (m := 2) (i := 1) (by norm_num)

/-! ### BE2 §11: finite-dimensional integral Krull–Schmidt input to Theorem 11.3 -/

open StringDiagrams StringDiagrams.KrullSchmidt in
example : Module.Free ℤ (K₀ (SKarAlg.FGProj (trivialGrading ℚ))) :=
  SKarAlg.fgProj_k0_free_int (trivialGrading ℚ)

open StringDiagrams in
example : Module.Free ℤ
    (K₀ (GSKar ℚ (SuperalgebraCat KrullSchmidtExamples.rationalGradedAlgebra.parity))) :=
  GSKarAlg.k0_free_int KrullSchmidtExamples.rationalGradedAlgebra

open StringDiagrams StringDiagrams.KrullSchmidt in
example (P Q : SKar ℚ (UnitSupercat ℚ)) :
    K₀.mk P = K₀.mk Q ↔ Nonempty (P ≅ Q) := mk_eq_mk_iff ℚ

open StringDiagrams in
example : K₀.mk (SKarUnit.obj ℚ 0) ≠ 0 := KrullSchmidtExamples.unitObj_class_ne_zero 0

end NonVacuity
