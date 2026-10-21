/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.KrullSchmidtParity
import StringDiagrams.Super.KrullSchmidtExamples
import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Type-M and type-Q parity-orbit consumers

The even rational field and the rational superalgebra with one odd generator
squaring to one exercise both directions of the corrected BE2 §11 parity-ring
criterion. All categorical finiteness and indecomposability inputs are proved.
-/

noncomputable section
namespace StringDiagrams.KrullSchmidtParityExamples
open CategoryTheory Limits Idempotents KrullSchmidt Module

attribute [-instance] SKar.instAlgebraZπ in
/-- The dimension equivalence for the even field, with the parity action
specified by `K₀.moduleZπ`, rather than inferred from a monoidal algebra. -/
def typeMDimension :
    letI := K₀.moduleZπ ℚ (SKar ℚ (UnitSupercat ℚ))
    K₀ (SKar ℚ (UnitSupercat ℚ)) ≃ₗ[Zπ] Zπ := by
  letI := K₀.moduleZπ ℚ (SKar ℚ (UnitSupercat ℚ))
  refine LinearEquiv.ofBijective
    { toFun := SKarUnit.K₀Dim ℚ
      map_add' := map_add _
      map_smul' := ?_ }
    ⟨SKarUnit.K₀Dim_injective, SKarUnit.K₀Dim_surjective⟩
  intro c x
  change SKarUnit.K₀Dim ℚ (c • x) = c * SKarUnit.K₀Dim ℚ x
  have hpi : Zπ.π • x = K₀.piInvolution ℚ (SKar ℚ (UnitSupercat ℚ)) x :=
    Zπ.π_smul _ _ x
  obtain ⟨a, d, rfl⟩ := Zπ.exists_eq_add_mul_π c
  rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul,
    hpi, map_add, map_zsmul, map_zsmul, SKarUnit.K₀Dim_piInvolution]
  simp only [zsmul_eq_mul]
  ring

/-- The concrete type-M example is free for the specified parity action. -/
theorem typeM_free :
    letI := K₀.moduleZπ ℚ (SKar ℚ (UnitSupercat ℚ))
    Module.Free Zπ (K₀ (SKar ℚ (UnitSupercat ℚ))) := by
  let := K₀.moduleZπ ℚ (SKar ℚ (UnitSupercat ℚ))
  exact Module.Free.of_basis ((Basis.singleton Unit Zπ).map typeMDimension.symm)

/-- Every indecomposable of the even field is non-self-associate under parity. -/
theorem typeM_no_parity_iso (X : SKar ℚ (UnitSupercat ℚ)) (hX : IsIndec X) :
    ¬ Nonempty ((PiCategory.pi (R := ℚ)).obj X ≅ X) :=
  (SKarAlg.k0_free_zpi_iff (trivialGrading ℚ)).1 typeM_free X hX

/-- A choice of order for selecting parity-orbit representatives. -/
@[instance_reducible]
def typeMOrder : LinearOrder (IndecClass (SKar ℚ (UnitSupercat ℚ))) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- An orbit-representative basis obtained by applying the corrected theorem
to the even rational field. The order only chooses one member of each pair. -/
def typeMPairedBasis :
    letI := typeMOrder
    letI := K₀.moduleZπ ℚ (SKar ℚ (UnitSupercat ℚ))
    Basis (ParityBasis.PairRep (indecParity ℚ (C := SKar ℚ (UnitSupercat ℚ))))
      Zπ (K₀ (SKar ℚ (UnitSupercat ℚ))) := by
  letI := typeMOrder
  exact parityBasis ℚ typeM_no_parity_iso

/-- The two-dimensional rational algebra `ℚ[c]/(c²-1)`, with `c` odd. -/
abbrev QAlgebra := AddMonoidAlgebra ℚ (ZMod 2)

/-- The homogeneous decomposition by the exponent of the odd generator. -/
abbrev qGrading : ZMod 2 → Submodule ℚ QAlgebra := AddMonoidAlgebra.grade ℚ

instance : FiniteDimensional ℚ QAlgebra :=
  Module.Finite.of_basis (AddMonoidAlgebra.basis (ZMod 2) ℚ)

abbrev QCat := SuperalgebraCat qGrading
abbrev QEven := Underlying ℚ (Envelope ℚ QCat)

/-- The even rank-one free module before additive idempotent completion. -/
def qPoint : QEven := ⟨⟨0, ()⟩⟩

/-- The regular rank-one projective of the odd-generator algebra. -/
def typeQObj : SKar ℚ QCat := (SKar.of ℚ QCat).obj qPoint

private theorem qEnd_single (e : qPoint ⟶ qPoint) :
    ∃ a : ℚ, (e.val : QAlgebra) = AddMonoidAlgebra.single 0 a := by
  have h : (e.val : QAlgebra) ∈ qGrading 0 := e.property
  obtain ⟨a, ha⟩ := (AddMonoidAlgebra.mem_grade_iff' ℚ 0 e.val).1 h
  exact ⟨a, ha.symm⟩

/-- The regular projective is indecomposable: its even endomorphism ring is ℚ. -/
theorem typeQ_indec : IsIndec typeQObj := by
  apply (isIndec_obj_iff (SKar.of ℚ QCat) qPoint).2
  constructor
  · intro hz
    have h := congrArg (fun e : qPoint ⟶ qPoint => (e.val : QAlgebra).coeff 0)
      ((IsZero.iff_id_eq_zero _).1 hz)
    change (1 : QAlgebra).coeff 0 = (0 : QAlgebra).coeff 0 at h
    simp at h
  · intro e he
    obtain ⟨a, ha⟩ := qEnd_single e
    let f : QAlgebra := e.val
    have hmul : f * f = f := congrArg Subtype.val he
    change f = AddMonoidAlgebra.single 0 a at ha
    rw [ha, AddMonoidAlgebra.single_mul_single, zero_add] at hmul
    have h : a * a = a := by
      simpa using congrArg (fun x : QAlgebra => x.coeff 0) hmul
    rcases mul_eq_zero.mp (show a * (a - 1) = 0 by rw [mul_sub, mul_one, h, sub_self]) with h | h
    · left
      apply Subtype.ext
      change f = (0 : QAlgebra)
      simpa only [h, AddMonoidAlgebra.single_zero] using ha
    · right
      apply Subtype.ext
      change f = (1 : QAlgebra)
      simpa only [sub_eq_zero.mp h, ← AddMonoidAlgebra.one_def] using ha

/-- Multiplication by the odd unit gives an even parity-shift isomorphism. -/
def qPointParityIso : (PiCategory.pi (R := ℚ)).obj qPoint ≅ qPoint where
  hom := ⟨AddMonoidAlgebra.single 1 1, AddMonoidAlgebra.single_mem_grade 1 1⟩
  inv := ⟨AddMonoidAlgebra.single 1 1, AddMonoidAlgebra.single_mem_grade 1 1⟩
  hom_inv_id := by
    apply Subtype.ext
    change (AddMonoidAlgebra.single 1 1 : QAlgebra) * AddMonoidAlgebra.single 1 1 = (1 : QAlgebra)
    rw [AddMonoidAlgebra.single_mul_single]
    rw [show (1 : ZMod 2) + 1 = 0 by decide, mul_one]
    exact AddMonoidAlgebra.one_def.symm
  inv_hom_id := by
    apply Subtype.ext
    change (AddMonoidAlgebra.single 1 1 : QAlgebra) * AddMonoidAlgebra.single 1 1 = (1 : QAlgebra)
    rw [AddMonoidAlgebra.single_mul_single]
    rw [show (1 : ZMod 2) + 1 = 0 by decide, mul_one]
    exact AddMonoidAlgebra.one_def.symm

/-- The regular projective is parity-self-isomorphic. -/
def typeQParityIso : (PiCategory.pi (R := ℚ)).obj typeQObj ≅ typeQObj := by
  have h : (PiCategory.pi (R := ℚ)).obj typeQObj =
      (SKar.of ℚ QCat).obj ((PiCategory.pi (R := ℚ)).obj qPoint) := by
    change (Karoubi.piFunctor (R := ℚ)).obj ((toKaroubi _).obj _) = _
    dsimp [Karoubi.piFunctor]
    simp only [CategoryTheory.Functor.map_id]
    rfl
  exact eqToIso h ≪≫ (SKar.of ℚ QCat).mapIso qPointParityIso

/-- A finite-dimensional superalgebra whose split K₀ is not parity-ring free.
This is a norm obstruction from an indecomposable, not merely a fixed vector. -/
theorem typeQ_not_free :
    letI := K₀.moduleZπ ℚ (SKar ℚ QCat)
    ¬ Module.Free Zπ (K₀ (SKar ℚ QCat)) :=
  KrullSchmidt.not_free_of_parity_iso ℚ typeQ_indec typeQParityIso

/-- The type-Q projective gives a nonzero class in the integral Tate quotient. -/
theorem typeQ_tate_ne_zero :
    letI := K₀.moduleZπ ℚ (SKar ℚ QCat)
    ∃ x : ParityBasis.fixedSubmodule (M := K₀ (SKar ℚ QCat)),
      Submodule.Quotient.mk x ≠ (0 : ParityBasis.TateZero (M := K₀ (SKar ℚ QCat))) := by
  let := K₀.moduleZπ ℚ (SKar ℚ QCat)
  have hx : Zπ.π • K₀.mk typeQObj = K₀.mk typeQObj := by
    rw [K₀.π_smul_mk]
    exact K₀.mk_eq_mk_of_iso typeQParityIso
  refine ⟨⟨K₀.mk typeQObj, hx⟩, ?_⟩
  intro h
  exact KrullSchmidt.indec_not_norm ℚ typeQ_indec typeQParityIso
    ((ParityBasis.tate_eq_zero_iff (K₀.mk typeQObj) hx).1 h)

#print axioms ParityBasis.free_iff
#print axioms KrullSchmidt.k0_free_zpi_iff
#print axioms KrullSchmidt.parityBasis
#print axioms GSKarAlg.k0_free_zpi_iff
#print axioms typeM_no_parity_iso
#print axioms typeMPairedBasis
#print axioms typeQ_not_free
#print axioms typeQ_tate_ne_zero

end StringDiagrams.KrullSchmidtParityExamples
