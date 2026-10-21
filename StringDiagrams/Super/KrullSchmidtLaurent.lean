/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.KrullSchmidt
import StringDiagrams.Super.LaurentBasis

/-!
# Laurent Krull–Schmidt bases

The corrected first preliminary fact of Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, §11, used in Theorems 11.3 and 11.7.
The category has finite-dimensional degree-zero Homs and the spaces of maps
from integer shifts of an indecomposable to itself vanish in sufficiently
negative degree. These are the categorical Hom-finiteness and lower-bound
hypotheses; neither shift rigidity nor a basis is assumed.

This theorem does not assert freeness over the larger parity coefficient ring.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Limits Idempotents Module LaurentPolynomial

namespace K₀
variable (k C : Type*) [CommRing k] [Category C] [Preadditive C]
    [Linear k C] [QPiCategory k C] [HasBinaryBiproducts C]

/-- Restrict the existing covering Laurent action to `ℤ[q,q⁻¹]`. -/
@[instance_reducible] def moduleLaurentInt : Module (LaurentPolynomial ℤ) (K₀ C) :=
  let := moduleLaurent k C
  Module.compHom (K₀ C) (AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ))

/-- Compatibility with the existing grading-shift unit, in every integer degree. -/
theorem int_T_smul (n : ℤ) (x : K₀ C) :
    letI := moduleLaurentInt k C
    (T n : LaurentPolynomial ℤ) • x =
      (((qUnit k C) ^ n : (AddMonoid.End (K₀ C))ˣ) : AddMonoid.End (K₀ C)) x := by
  change laurentEnd k C
    (AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) (T n)) x = _
  rw [T, AddMonoidAlgebra.mapRingHom_single, map_one, ← T, laurentEnd_T]

end K₀

namespace KrullSchmidt
variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C]
    [Linear k C] [QPiCategory k C]

/-- An additive equivalence permutes indecomposable isomorphism classes. -/
def indecEquiv (e : C ≌ C) [e.functor.Additive] [e.inverse.Additive] :
    Equiv.Perm (IndecClass C) where
  toFun := Quotient.map (fun X => ⟨e.functor.obj X.val,
    (isIndec_obj_iff e.functor X.val).2 X.property⟩)
    (fun _ _ ⟨f⟩ => ⟨e.functor.mapIso f⟩)
  invFun := Quotient.map (fun X => ⟨e.inverse.obj X.val,
    (isIndec_obj_iff e.inverse X.val).2 X.property⟩)
    (fun _ _ ⟨f⟩ => ⟨e.inverse.mapIso f⟩)
  left_inv := by
    intro i
    induction i using Quotient.inductionOn with
    | h X => exact Quotient.sound ⟨(e.unitIso.app X.val).symm⟩
  right_inv := by
    intro i
    induction i using Quotient.inductionOn with
    | h X => exact Quotient.sound ⟨e.counitIso.app X.val⟩

/-- The shift permutation of indecomposable classes. -/
def indecQ : Equiv.Perm (IndecClass C) := by
  let e := QPiCategory.qEquivalence k C
  have : e.functor.Additive := QPiCategory.Q_additive
  have : e.inverse.Additive := QPiCategory.Qinv_additive
  exact indecEquiv e

/-- The integer shift of an indecomposable class. -/
def indecShift (n : ℤ) (i : IndecClass C) : IndecClass C := (indecQ k ^ n) i

/-- Integer grading shifts acting on indecomposable classes. -/
@[instance_reducible] def indecShiftAction : AddAction ℤ (IndecClass C) where
  vadd n i := (indecQ k ^ n) i
  zero_vadd i := by
    change (indecQ k ^ (0 : ℤ)) i = i
    simp
  add_vadd m n i := by
    change (indecQ k ^ (m + n)) i = (indecQ k ^ m) ((indecQ k ^ n) i)
    simp [zpow_add, Equiv.Perm.mul_apply]

/-- Shifted representative objects agree up to isomorphism. -/
theorem indecQ_rep_iso (i : IndecClass C) :
    Nonempty ((QPiCategory.Q (R := k)).obj i.rep ≅ (indecQ k i).rep) := by
  let e := QPiCategory.qEquivalence k C
  have : e.functor.Additive := QPiCategory.Q_additive
  have h : indecQ k i = Quotient.mk (indecSetoid C)
      ⟨(QPiCategory.Q (R := k)).obj i.rep,
        (isIndec_obj_iff e.functor i.rep).2
          i.isIndec_rep⟩ := by
    conv_lhs => rw [← Quotient.out_eq i]
    rfl
  rw [h]
  exact IndecClass.exists_iso_rep _

variable [HasBinaryBiproducts C]

/-- Grading shift permutes the integral indecomposable classes. -/
theorem int_T_one_smul_indec (i : IndecClass C) :
    letI := K₀.moduleLaurentInt k C
    (T 1 : LaurentPolynomial ℤ) • K₀.mk i.rep = K₀.mk (indecQ k i).rep := by
  let := K₀.moduleLaurentInt k C
  rw [K₀.int_T_smul, zpow_one]
  change K₀.map (QPiCategory.Q (R := k)) (K₀.mk i.rep) = _
  rw [K₀.map_mk]
  exact K₀.mk_eq_mk_of_iso (indecQ_rep_iso k i).some

/-- The compatibility in every integer degree, including negative shifts. -/
theorem int_T_smul_indec (n : ℤ) (i : IndecClass C) :
    letI := K₀.moduleLaurentInt k C
    (T n : LaurentPolynomial ℤ) • K₀.mk i.rep = K₀.mk (indecShift k n i).rep := by
  let := K₀.moduleLaurentInt k C
  let := indecShiftAction k (C := C)
  change (T n : LaurentPolynomial ℤ) • K₀.mk i.rep = K₀.mk (n +ᵥ i).rep
  induction n using Int.induction_on generalizing i with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1 : ℤ) = 1 + n by omega, T_add, mul_smul, ih,
      int_T_one_smul_indec, add_vadd]
    change K₀.mk ((indecQ k) (_ +ᵥ i)).rep =
      K₀.mk ((indecQ k ^ (1 : ℤ)) (_ +ᵥ i)).rep
    rw [zpow_one]
  | pred n ih =>
    have inj : Function.Injective (fun x : K₀ C => (T 1 : LaurentPolynomial ℤ) • x) := by
      intro x y h
      have h' := congrArg (fun x : K₀ C => (T (-1) : LaurentPolynomial ℤ) • x) h
      simpa only [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul] using h'
    apply inj
    dsimp only
    rw [← mul_smul, ← T_add, show (1 + (-(n : ℤ) - 1)) = -(n : ℤ) by omega, ih,
      int_T_one_smul_indec]
    have heq : (indecQ k) ((-(n : ℤ) - 1) +ᵥ i) = -(n : ℤ) +ᵥ i := by
      change (indecQ k) ((indecQ k ^ (-(n : ℤ) - 1)) i) = _
      rw [← Equiv.Perm.mul_apply, ← zpow_one_add, show (1 + (-(n : ℤ) - 1)) = -(n : ℤ) by omega]
      rfl
    rw [heq]

/-- Boundedness below of the graded endomorphism spaces, written entirely in
the degree-zero category: degree `n` maps are maps from `Qⁿ X` to `X`.
Representatives do not affect this vanishing condition. -/
def ShiftHomBoundedBelow : Prop :=
  ∀ i : IndecClass C, ∃ N : ℤ, ∀ n < N, Subsingleton ((indecShift k n i).rep ⟶ i.rep)

omit [HasBinaryBiproducts C] in
/-- The categorical lower bound forces integer-shift rigidity. -/
theorem indec_shift_free (h : ShiftHomBoundedBelow k (C := C)) :
    ∀ (i : IndecClass C) (n : ℤ), indecShift k n i = i → n = 0 := by
  let := indecShiftAction k (C := C)
  apply LaurentBasis.free_of_boundedBelow
  intro i
  obtain ⟨N, hN⟩ := h i
  refine ⟨N, fun n hn => ?_⟩
  by_contra hlt
  have hzero := hN n (by omega)
  change Subsingleton ((n +ᵥ i).rep ⟶ i.rep) at hzero
  rw [hn] at hzero
  have hid : (𝟙 i.rep : i.rep ⟶ i.rep) = 0 := hzero.elim _ _
  exact i.isIndec_rep.1 ((IsZero.iff_id_eq_zero i.rep).2 hid)

variable [HomFinite k C] [IsIdempotentComplete C]

/-- The Laurent basis on integer-shift orbits of indecomposables. This retains
parity-self-associate indecomposables; no type-M condition is required. -/
def laurentBasis (h : ShiftHomBoundedBelow k (C := C)) :
    letI := K₀.moduleLaurentInt k C
    letI := indecShiftAction k (C := C)
    Basis (LaurentBasis.Orbit (ι := IndecClass C)) (LaurentPolynomial ℤ) (K₀ C) := by
  let := K₀.moduleLaurentInt k C
  let := indecShiftAction k (C := C)
  exact LaurentBasis.ofOrbits (indecBasis k)
    (fun n i => by
      simp only [indecBasis_apply]
      exact int_T_smul_indec k n i)
    (indec_shift_free k h)

@[simp] theorem laurentBasis_apply (h : ShiftHomBoundedBelow k (C := C))
    (o : @Quotient (IndecClass C) (@AddAction.orbitRel ℤ _ _ (indecShiftAction k))) :
    laurentBasis k h o = K₀.mk o.out.rep := by
  let := K₀.moduleLaurentInt k C
  let := indecShiftAction k (C := C)
  unfold laurentBasis
  rw [LaurentBasis.ofOrbits_apply]
  exact indecBasis_apply k o.out

/-- `R`-freeness needed by BE2 Theorem 11.7, under the categorical Laurentian
Hom hypotheses, rather than the false general covering-ring freeness claim. -/
theorem k0_free_laurentInt (h : ShiftHomBoundedBelow k (C := C)) :
    letI := K₀.moduleLaurentInt k C
    Module.Free (LaurentPolynomial ℤ) (K₀ C) := by
  let := K₀.moduleLaurentInt k C
  exact Module.Free.of_basis (laurentBasis k h)

end KrullSchmidt
end StringDiagrams
