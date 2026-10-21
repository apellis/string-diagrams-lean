/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.KrullSchmidt
import StringDiagrams.Super.ParityBasis

/-!
# Parity orbits in split Grothendieck groups

The parity-ring correction to the first preliminary fact of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §11 (used in Theorem 11.3).
For a Hom-finite idempotent-complete additive Π-category, `K₀` is free over
`Zπ` exactly when no nonzero indecomposable is isomorphic to its parity shift.
The integral basis and the parity permutation are derived, not hypotheses.

This applies in particular to the existing super and graded-super Karoubi
envelopes of finite-dimensional algebras. It does not yet assert freeness over
the Laurent coefficient ring: integer-shift rigidity and a basis modulo integer
shifts are separate remaining steps.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Limits Idempotents Module

namespace KrullSchmidt
universe u v
variable (k : Type*) [Field k] {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear k C] [PiCategory k C]

/-- The parity functor is a self-equivalence. -/
def parityEquivalence : C ≌ C where
  functor := PiCategory.pi (R := k)
  inverse := PiCategory.pi (R := k)
  unitIso := (PiCategory.ξ (R := k)).symm
  counitIso := PiCategory.ξ (R := k)
  functor_unitIso_comp X := by
    change (PiCategory.pi (R := k)).map ((PiCategory.ξ (R := k)).inv.app X) ≫ _ = _
    rw [← PiCategory.ξ_inv_pi]
    exact (PiCategory.ξ (R := k)).inv_hom_id_app _

/-- Parity preserves indecomposability. -/
theorem isIndec_pi_iff (X : C) :
    IsIndec ((PiCategory.pi (R := k)).obj X) ↔ IsIndec X := by
  let e := parityEquivalence k (C := C)
  have : e.functor.Additive := PiCategory.pi_additive
  exact isIndec_obj_iff e.functor X

/-- The parity permutation of indecomposable isomorphism classes. -/
def indecParity : IndecClass C → IndecClass C :=
  Quotient.map (fun X => ⟨(PiCategory.pi (R := k)).obj X.val,
    (isIndec_pi_iff k X.val).2 X.property⟩)
    (fun _ _ ⟨e⟩ => ⟨(PiCategory.pi (R := k)).mapIso e⟩)

/-- The representative of the parity class is isomorphic to the parity shift. -/
theorem indecParity_rep_iso (i : IndecClass C) :
    Nonempty ((PiCategory.pi (R := k)).obj i.rep ≅ (indecParity k i).rep) := by
  have h : indecParity k i = Quotient.mk (indecSetoid C)
      ⟨(PiCategory.pi (R := k)).obj i.rep, (isIndec_pi_iff k i.rep).2 i.isIndec_rep⟩ := by
    conv_lhs => rw [← Quotient.out_eq i]
    rfl
  rw [h]
  exact IndecClass.exists_iso_rep _

/-- Parity acts involutively on the integral basis indices. -/
theorem indecParity_involutive : Function.Involutive (indecParity k (C := C)) := by
  intro i
  apply IndecClass.eq_of_iso
  exact (indecParity_rep_iso k (indecParity k i)).some.symm ≪≫
    (PiCategory.pi (R := k)).mapIso (indecParity_rep_iso k i).some.symm ≪≫
    PiCategory.ξApp i.rep

/-- Fixed indecomposable classes are precisely parity-self-isomorphic objects. -/
theorem indecParity_eq_iff (i : IndecClass C) :
    indecParity k i = i ↔ Nonempty ((PiCategory.pi (R := k)).obj i.rep ≅ i.rep) := by
  constructor
  · intro h
    simpa only [h] using indecParity_rep_iso k i
  · rintro ⟨e⟩
    exact IndecClass.eq_of_iso ((indecParity_rep_iso k i).some.symm ≪≫ e)

variable [HasBinaryBiproducts C]

/-- On the existing split Grothendieck group, parity permutes the indecomposable
classes; this is compatible with `K₀.moduleZπ`. -/
theorem pi_smul_indec (i : IndecClass C) :
    letI := K₀.moduleZπ k C
    Zπ.π • K₀.mk i.rep = K₀.mk (indecParity k i).rep := by
  let := K₀.moduleZπ k C
  rw [K₀.π_smul_mk]
  exact K₀.mk_eq_mk_of_iso (indecParity_rep_iso k i).some

variable [HomFinite k C] [IsIdempotentComplete C]

/-- Corrected parity-ring freeness criterion. There is no assumed basis or
orbit decomposition, and no finiteness restriction on the indecomposable set. -/
theorem k0_free_zpi_iff :
    letI := K₀.moduleZπ k C
    Module.Free Zπ (K₀ C) ↔
    ∀ X : C, IsIndec X → ¬ Nonempty ((PiCategory.pi (R := k)).obj X ≅ X) := by
  let := K₀.moduleZπ k C
  rw [ParityBasis.free_iff (indecBasis k) (indecParity k) (indecParity_involutive k)
    (fun i => by simpa only [indecBasis_apply] using pi_smul_indec k i)]
  constructor
  · intro h X hX ⟨e⟩
    let i : IndecClass C := Quotient.mk (indecSetoid C) ⟨X, hX⟩
    let f : X ≅ i.rep := (IndecClass.exists_iso_rep hX).some
    exact h i ((indecParity_eq_iff k i).2
      ⟨(PiCategory.pi (R := k)).mapIso f.symm ≪≫ e ≪≫ f⟩)
  · intro h i hi
    exact h i.rep i.isIndec_rep ((indecParity_eq_iff k i).1 hi)

/-- A type-Q indecomposable gives a nonzero fixed-point-modulo-norm obstruction;
it rules out freeness even in infinite rank. -/
theorem not_free_of_parity_iso {X : C} (hX : IsIndec X)
    (e : (PiCategory.pi (R := k)).obj X ≅ X) :
    letI := K₀.moduleZπ k C
    ¬ Module.Free Zπ (K₀ C) :=
  fun h => (k0_free_zpi_iff k).1 h X hX ⟨e⟩

/-- The class of a parity-self-isomorphic indecomposable is not a norm in the
split Grothendieck group. Its class in the fixed-point-modulo-norm quotient
therefore cannot vanish. -/
theorem indec_not_norm {X : C} (hX : IsIndec X)
    (e : (PiCategory.pi (R := k)).obj X ≅ X) :
    letI := K₀.moduleZπ k C
    ¬ ∃ y : K₀ C, y + Zπ.π • y = K₀.mk X := by
  let := K₀.moduleZπ k C
  let i : IndecClass C := Quotient.mk (indecSetoid C) ⟨X, hX⟩
  let f : X ≅ i.rep := (IndecClass.exists_iso_rep hX).some
  have hi : indecParity k i = i := (indecParity_eq_iff k i).2
    ⟨(PiCategory.pi (R := k)).mapIso f.symm ≪≫ e ≪≫ f⟩
  have h := ParityBasis.fixed_not_norm (indecBasis k) (indecParity k)
    (indecParity_involutive k)
    (fun j => by simpa only [indecBasis_apply] using pi_smul_indec k j) i hi
  simpa only [indecBasis_apply, ← K₀.mk_eq_mk_of_iso f] using h

/-- Chosen representatives of paired indecomposable classes give a parity-ring
basis when there are no parity-self-isomorphic indecomposables. -/
def parityBasis [LinearOrder (IndecClass C)]
    (h : ∀ X : C, IsIndec X → ¬ Nonempty ((PiCategory.pi (R := k)).obj X ≅ X)) :
    letI := K₀.moduleZπ k C
    Basis (ParityBasis.PairRep (indecParity k (C := C))) Zπ (K₀ C) := by
  letI := K₀.moduleZπ k C
  exact ParityBasis.pairedBasis (indecBasis k) (indecParity k) (indecParity_involutive k)
    (fun i => by simpa only [indecBasis_apply] using pi_smul_indec k i)
    (fun i hi => h i.rep i.isIndec_rep ((indecParity_eq_iff k i).1 hi))

@[simp] theorem parityBasis_apply [LinearOrder (IndecClass C)]
    (h : ∀ X : C, IsIndec X → ¬ Nonempty ((PiCategory.pi (R := k)).obj X ≅ X))
    (i : ParityBasis.PairRep (indecParity k (C := C))) :
    parityBasis k h i = K₀.mk i.val.rep := by
  let := K₀.moduleZπ k C
  exact (ParityBasis.pairedBasis_apply _ _ _ _ _ _).trans (indecBasis_apply k i.val)

end KrullSchmidt

namespace SKarAlg
variable {k A : Type*} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (𝒜 : ZMod 2 → Submodule k A) [GradedAlgebra 𝒜]
local instance : Module Zπ (K₀ (SKar k (SuperalgebraCat 𝒜))) :=
  K₀.moduleZπ k _

/-- The finite-dimensional superalgebra case of the corrected parity freeness
criterion, on the existing super Karoubi envelope. -/
theorem k0_free_zpi_iff : Module.Free Zπ (K₀ (SKar k (SuperalgebraCat 𝒜))) ↔
    ∀ X : SKar k (SuperalgebraCat 𝒜), KrullSchmidt.IsIndec X →
      ¬ Nonempty ((PiCategory.pi (R := k)).obj X ≅ X) :=
  KrullSchmidt.k0_free_zpi_iff k
end SKarAlg

namespace GSKarAlg
variable {k A : Type*} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (𝒢 : GradedSuperalgebra k A)
local instance : Module Zπ (K₀ (GSKar k (SuperalgebraCat 𝒢.parity))) :=
  K₀.moduleZπ k _

/-- The parity-ring criterion also applies before quotienting integer shifts
in the graded-super envelope. This is not a Laurent-ring freeness assertion. -/
theorem k0_free_zpi_iff : Module.Free Zπ (K₀ (GSKar k (SuperalgebraCat 𝒢.parity))) ↔
    ∀ X : GSKar k (SuperalgebraCat 𝒢.parity), KrullSchmidt.IsIndec X →
      ¬ Nonempty ((PiCategory.pi (R := k)).obj X ≅ X) :=
  KrullSchmidt.k0_free_zpi_iff k
end GSKarAlg

end StringDiagrams
