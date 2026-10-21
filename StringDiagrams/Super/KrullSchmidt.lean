/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Karoubi.KrullSchmidtDecomposition
import StringDiagrams.Super.SKarSuperalgebraK0
import StringDiagrams.Super.GSKar
import StringDiagrams.Super.GSMod

/-!
# Integral Krull–Schmidt bases for finite-dimensional superalgebras

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §11,
first preliminary fact used in Theorem 11.3. We prove its integral-basis assertion
for the existing super and graded super Karoubi envelopes of a finite-dimensional
superalgebra. Hom-finiteness is proved from the algebra's finite dimension, not
assumed on the completed category.

This is the finite-dimensional case, not the general Laurentian case. No freeness
over `Zπ` or `LaurentPolynomial Zπ` is asserted. The integral basis retains all
parity and grading shifts as distinct indices when they are not isomorphic.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Limits Idempotents
open KrullSchmidt

universe w u v
variable {k : Type w} [Field k]

namespace KrullSchmidt

instance homFinite_mat {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [HomFinite k C] : HomFinite k (Mat_ C) where
  finiteDimensional M N := by
    change FiniteDimensional k (∀ i j, M.X i ⟶ N.X j)
    infer_instance

instance homFinite_karoubi {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [HomFinite k C] : HomFinite k (Karoubi C) where
  finiteDimensional P Q := by
    let f : (P ⟶ Q) →ₗ[k] (P.X ⟶ Q.X) :=
      { toFun := fun f => f.f
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective f (fun x y h => Karoubi.hom_ext x y h)

instance homFinite_envelope {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [HomFinite k C] : HomFinite k (Envelope k C) where
  finiteDimensional X Y := HomFinite.finiteDimensional X.obj Y.obj

instance homFinite_qEnvelope {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [HomFinite k C] : HomFinite k (QEnvelope k C) where
  finiteDimensional X Y := HomFinite.finiteDimensional X.obj Y.obj

instance homFinite_underlying {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [Supercategory k C] [HomFinite k C] : HomFinite k (Underlying k C) where
  finiteDimensional X Y := by
    change FiniteDimensional k (Supercategory.parity (R := k) X.obj Y.obj 0)
    infer_instance

instance homFinite_degreeZero {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [Supercategory k C] [GradedSupercategory k C] [HomFinite k C] :
    HomFinite k (GradedSupercategory.DegreeZero k C) where
  finiteDimensional X Y := by
    change FiniteDimensional k (GradedSupercategory.degree (R := k) X.obj Y.obj 0)
    infer_instance

instance homFinite_superalgebra {A : Type u} [Ring A] [Algebra k A]
    [FiniteDimensional k A] (𝒜 : ZMod 2 → Submodule k A) :
    HomFinite k (SuperalgebraCat 𝒜) where
  finiteDimensional _ _ := inferInstanceAs (FiniteDimensional k A)

end KrullSchmidt

namespace SKarAlg
variable {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (𝒜 : ZMod 2 → Submodule k A) [GradedAlgebra 𝒜]

/-- The indecomposable integral basis for the super Karoubi envelope of a
finite-dimensional superalgebra; no type-M hypothesis is needed. -/
def indecBasis : Module.Basis (IndecClass (SKar k (SuperalgebraCat 𝒜))) ℤ
    (K₀ (SKar k (SuperalgebraCat 𝒜))) := KrullSchmidt.indecBasis k

@[simp] theorem indecBasis_apply (b : IndecClass (SKar k (SuperalgebraCat 𝒜))) :
    indecBasis 𝒜 b = K₀.mk b.rep := KrullSchmidt.indecBasis_apply k b

/-- Integral freeness, not freeness over the parity coefficient ring. -/
theorem k0_free_int : Module.Free ℤ (K₀ (SKar k (SuperalgebraCat 𝒜))) :=
  Module.Free.of_basis (indecBasis 𝒜)
end SKarAlg

namespace SKarAlg
variable {A : Type w} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (𝒜 : ZMod 2 → Submodule k A) [GradedAlgebra 𝒜]

/-- The integral indecomposable basis on the split K₀ of finitely generated
projective right supermodules (even retracts of finite parity-shifted free modules).
The index set is transported through the existing `SKar` equivalence. -/
def fgProjIndecBasis : Module.Basis (IndecClass (SKar k (SuperalgebraCat 𝒜))) ℤ
    (K₀ (FGProj 𝒜)) := (indecBasis 𝒜).map (K₀Equiv 𝒜).toIntLinearEquiv

@[simp] theorem fgProjIndecBasis_apply (b : IndecClass (SKar k (SuperalgebraCat 𝒜))) :
    fgProjIndecBasis 𝒜 b = K₀.mk ((toFGProj 𝒜).obj b.rep) := by
  simp [fgProjIndecBasis, K₀Equiv_mk]

omit [FiniteDimensional k A] in
/-- Every basis vector is the class of an indecomposable projective supermodule. -/
theorem isIndec_fgProj_rep (b : IndecClass (SKar k (SuperalgebraCat 𝒜))) :
    IsIndec ((toFGProj 𝒜).obj b.rep) :=
  (isIndec_obj_iff (toFGProj 𝒜) b.rep).2 b.isIndec_rep

/-- Integral freeness for finitely generated projective right supermodules. -/
theorem fgProj_k0_free_int : Module.Free ℤ (K₀ (FGProj 𝒜)) :=
  Module.Free.of_basis (fgProjIndecBasis 𝒜)

/-- Every projective supermodule is a finite sum of indecomposables under the
existing additive equivalence; no decomposition or basis is an input. -/
theorem fgProj_exists_iso_sumList (P : FGProj 𝒜) :
    ∃ l : List (IndecClass (SKar k (SuperalgebraCat 𝒜))),
      Nonempty (P ≅ (toFGProj 𝒜).obj (sumList l)) := by
  let e := (toFGProj 𝒜).asEquivalence
  obtain ⟨l, ⟨h⟩⟩ := exists_iso_sumList k (e.inverse.obj P)
  exact ⟨l, ⟨(e.counitIso.app P).symm ≪≫ (toFGProj 𝒜).mapIso h⟩⟩
end SKarAlg

namespace GSKarAlg
variable {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (𝒢 : GradedSuperalgebra k A)

/-- The finite-dimensional integral-basis part of BE2 §11's first preliminary
fact, an input to Theorem 11.3. The category is the existing graded super Karoubi
envelope; the statement does not assert a covering-ring basis. -/
def indecBasis : Module.Basis (IndecClass (GSKar k (SuperalgebraCat 𝒢.parity))) ℤ
    (K₀ (GSKar k (SuperalgebraCat 𝒢.parity))) := KrullSchmidt.indecBasis k

@[simp] theorem indecBasis_apply (b : IndecClass (GSKar k (SuperalgebraCat 𝒢.parity))) :
    indecBasis 𝒢 b = K₀.mk b.rep := KrullSchmidt.indecBasis_apply k b

/-- The split Grothendieck group of the graded super Karoubi envelope of a
finite-dimensional graded superalgebra is free over ℤ. -/
theorem k0_free_int : Module.Free ℤ (K₀ (GSKar k (SuperalgebraCat 𝒢.parity))) :=
  Module.Free.of_basis (indecBasis 𝒢)
end GSKarAlg

end StringDiagrams
