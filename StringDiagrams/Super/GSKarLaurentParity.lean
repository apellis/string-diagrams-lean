/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.GSKarLaurent
import StringDiagrams.Super.KrullSchmidtLaurentParity

/-!
# Mixed Laurent decomposition for graded additive Karoubi envelopes

The corrected first preliminary fact of BE2 §11: degreewise finite-dimensional,
bounded-below graded Homs imply the M/Q decomposition on the existing split K₀.
The graded-superalgebra consumer is an input for Theorem 11.3; completed graded
2-supercategory homs supply the target input for Theorem 11.7. An equivalence
with graded left projectives is a separate comparison.
-/

noncomputable section
namespace StringDiagrams
namespace GSKar
open CategoryTheory
variable {k C : Type*} [Field k] [Category C] [Preadditive C] [Linear k C]
  [Supercategory k C] [GradedSupercategory k C] [DegreeHomFinite (k := k) (C := C)]

/-- The mixed ℒ-module decomposition derived from actual graded Hom bounds. -/
def laurentDecomposition (h : HomBoundedBelow (k := k) (C := C)) :=
  KrullSchmidt.laurentDecomposition k (shiftHomBoundedBelow h)

end GSKar
namespace GSKarAlg
variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The Laurentian graded-superalgebra form of the corrected BE2 §11 input. -/
def laurentDecomposition (𝒢 : GradedSuperalgebra k A)
    (hfin : ∀ n : ℤ, FiniteDimensional k (𝒢.degree n))
    (hbelow : ∃ N : ℤ, ∀ n < N, 𝒢.degree n = ⊥) :=
  letI : GSKar.DegreeHomFinite (k := k) (C := SuperalgebraCat 𝒢.parity) :=
    ⟨fun _ _ n => hfin n⟩
  GSKar.laurentDecomposition (k := k) (C := SuperalgebraCat 𝒢.parity) (fun _ _ => hbelow)

end GSKarAlg
end StringDiagrams
