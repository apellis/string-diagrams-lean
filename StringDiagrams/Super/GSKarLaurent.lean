/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.KrullSchmidtLaurent
import StringDiagrams.Karoubi.EquivalencePowers

/-!
# Laurentian bounds in graded additive Karoubi envelopes

The envelope form of the first preliminary fact in Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §11. Finite matrices
and their retracts preserve degreewise finite dimensionality and lower bounds.
This supplies the hypotheses of the Laurent basis theorem used in 11.3 and 11.7.
-/

noncomputable section
namespace StringDiagrams.GSKar
open CategoryTheory Limits Idempotents GradedSupercategory Supercategory

variable {k C : Type*} [Field k] [Category C] [Preadditive C] [Linear k C]
  [Supercategory k C] [GradedSupercategory k C]

/-- The even degree-zero category of formal shifts. -/
abbrev ShiftBase (k : Type*) (C : Type*) [Field k] [Category C]
    [Preadditive C] [Linear k C] [Supercategory k C] [GradedSupercategory k C] :=
  GUnderlying k (QPiEnvelope k C)

/-- Integer powers of the existing grading equivalence on formal shifts. -/
abbrev baseShift (n : ℤ) : ShiftBase k C ⥤ ShiftBase k C :=
  EquivalencePowers.pow (QPiCategory.qEquivalence k (ShiftBase k C)) n

instance (n : ℤ) : (baseShift (k := k) (C := C) n).Additive := by
  let e := QPiCategory.qEquivalence k (ShiftBase k C)
  have : e.functor.Additive := QPiCategory.Q_additive
  have : e.inverse.Additive := QPiCategory.Qinv_additive
  exact EquivalencePowers.pow_additive e n

/-- Integer shifts transported through the existing additive and Karoubi functors. -/
abbrev shiftFunctor (n : ℤ) : GSKar k C ⥤ GSKar k C :=
  Karoubi.mapFunctor (baseShift (k := k) (C := C) n).mapMat_

instance (n : ℤ) : (shiftFunctor (k := k) (C := C) n).Additive where
  map_add := by
    intros
    apply Karoubi.hom_ext
    exact (baseShift (k := k) (C := C) n).mapMat_.map_add

/-- The zero power transported to the completed category. -/
def shiftZeroIso : shiftFunctor (k := k) (C := C) 0 ≅ 𝟭 (GSKar k C) :=
  Karoubi.mapIsoId (Mat_.mapMatIso (Iso.refl (𝟭 (ShiftBase k C))))

/-- Applying the chosen shift after an integer power. -/
def shiftSuccIso (n : ℤ) :
    shiftFunctor (k := k) (C := C) n ⋙ QPiCategory.Q (R := k) ≅ shiftFunctor (n + 1) :=
  Karoubi.mapIso (Mat_.mapMatIso
    (F := baseShift n ⋙ QPiCategory.Q (R := k))
    (EquivalencePowers.succ (QPiCategory.qEquivalence k (ShiftBase k C)) n))

/-- Object coordinates of positive powers of the existing grading shift. -/
theorem baseShift_nat_obj (n : ℕ) (X : ShiftBase k C) :
    (EquivalencePowers.powNat (QPiCategory.qEquivalence k (ShiftBase k C)) n).obj X =
      ⟨⟨⟨X.obj.obj.par, ⟨X.obj.obj.obj.shift + n, X.obj.obj.obj.obj⟩⟩⟩⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    change (QPiCategory.Q (R := k)).obj
      ((EquivalencePowers.powNat (QPiCategory.qEquivalence k (ShiftBase k C)) n).obj X) = _
    rw [ih]
    change (⟨⟨⟨X.obj.obj.par, ⟨(X.obj.obj.obj.shift + n) + 1,
      X.obj.obj.obj.obj⟩⟩⟩⟩ : ShiftBase k C) = _
    congr 4; omega

/-- Object coordinates of negative powers of the existing inverse shift. -/
theorem baseShift_neg_obj (n : ℕ) (X : ShiftBase k C) :
    (EquivalencePowers.powNeg (QPiCategory.qEquivalence k (ShiftBase k C)) n).obj X =
      ⟨⟨⟨X.obj.obj.par, ⟨X.obj.obj.obj.shift - n, X.obj.obj.obj.obj⟩⟩⟩⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    change (QPiCategory.Qinv (R := k)).obj
      ((EquivalencePowers.powNeg (QPiCategory.qEquivalence k (ShiftBase k C)) n).obj X) = _
    rw [ih]
    change (⟨⟨⟨X.obj.obj.par, ⟨(X.obj.obj.obj.shift - n) - 1,
      X.obj.obj.obj.obj⟩⟩⟩⟩ : ShiftBase k C) = _
    congr 4; omega

/-- Object coordinates of the generic integer power; no new shift action is defined. -/
theorem baseShift_obj (n : ℤ) (X : ShiftBase k C) :
    (baseShift n).obj X =
      ⟨⟨⟨X.obj.obj.par, ⟨X.obj.obj.obj.shift + n, X.obj.obj.obj.obj⟩⟩⟩⟩ := by
  cases n with
  | ofNat n => exact baseShift_nat_obj n X
  | negSucc n =>
    change (EquivalencePowers.powNeg _ (n + 1)).obj X = _
    rw [baseShift_neg_obj]
    congr 4

/-- Degreewise Hom-finiteness of the original graded category. -/
class DegreeHomFinite : Prop where
  finiteDimensional (X Y : C) (n : ℤ) : FiniteDimensional k (degree (R := k) X Y n)

attribute [instance] DegreeHomFinite.finiteDimensional

instance [DegreeHomFinite (k := k) (C := C)] : KrullSchmidt.HomFinite k (ShiftBase k C) where
  finiteDimensional X Y := by
    let f : (X ⟶ Y) →ₗ[k] degree (R := k) X.obj.obj.obj.obj Y.obj.obj.obj.obj
        (0 + (X.obj.obj.obj.shift - Y.obj.obj.obj.shift)) :=
      { toFun := fun f => ⟨f.val.val, f.val.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective f (by
      intro a b h
      apply Subtype.ext
      exact h)

/-- The completed degree-zero category is Hom-finite under degreewise,
not total, finite dimensionality of the original graded Homs. -/
instance [DegreeHomFinite (k := k) (C := C)] : KrullSchmidt.HomFinite k (GSKar k C) :=
  inferInstanceAs (KrullSchmidt.HomFinite k (Karoubi (Mat_ (ShiftBase k C))))

/-- Formal shifts realize every Laurent monomial on the existing K₀. -/
theorem int_T_smul_mk (n : ℤ) (P : GSKar k C) :
    letI := K₀.moduleLaurentInt k (GSKar k C)
    (LaurentPolynomial.T n : LaurentPolynomial ℤ) • K₀.mk P =
      K₀.mk ((shiftFunctor n).obj P) := by
  let := K₀.moduleLaurentInt k (GSKar k C)
  open LaurentPolynomial in
  induction n using Int.induction_on with
  | zero =>
    simp only [T_zero, one_smul]
    exact K₀.mk_eq_mk_of_iso (shiftZeroIso.app P).symm
  | succ n ih =>
    rw [show (n + 1 : ℤ) = 1 + n by omega, T_add, mul_smul, ih,
      K₀.int_T_one_smul_mk]
    simpa only [add_comm (1 : ℤ), Functor.comp_obj] using K₀.mk_eq_mk_of_iso ((shiftSuccIso (n : ℤ)).app P)
  | pred n ih =>
    have inj : Function.Injective (fun x : K₀ (GSKar k C) =>
        (T 1 : LaurentPolynomial ℤ) • x) := by
      intro x y h
      have h' := congrArg (fun x : K₀ (GSKar k C) => (T (-1) : LaurentPolynomial ℤ) • x) h
      simpa only [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul] using h'
    apply inj
    dsimp only
    rw [← mul_smul, ← T_add, show 1 + (-(n : ℤ) - 1) = -(n : ℤ) by omega,
      ih, K₀.int_T_one_smul_mk]
    exact K₀.mk_eq_mk_of_iso (((shiftSuccIso (-(n : ℤ) - 1)).app P) ≪≫
      eqToIso (by congr 2; omega)).symm

/-- A lower degree bound for every original Hom-space. -/
def HomBoundedBelow : Prop :=
  ∀ X Y : C, ∃ N : ℤ, ∀ n < N, degree (R := k) X Y n = ⊥

/-- Matrices and retracts preserve the lower bound on shifted Homs. -/
theorem shift_hom_boundedBelow (h : HomBoundedBelow (k := k) (C := C))
    (P Q : GSKar k C) :
    ∃ N : ℤ, ∀ n < N, Subsingleton ((shiftFunctor n).obj P ⟶ Q) := by
  classical
  choose N hN using h
  let bounds : P.X.ι × Q.X.ι → ℤ := fun ij =>
    N (P.X.X ij.1).obj.obj.obj.obj (Q.X.X ij.2).obj.obj.obj.obj -
      (P.X.X ij.1).obj.obj.obj.shift + (Q.X.X ij.2).obj.obj.obj.shift
  obtain ⟨B, hB⟩ := (Set.finite_range bounds).bddBelow
  refine ⟨B, fun n hn => ⟨fun f g => ?_⟩⟩
  have zero : ∀ f : (shiftFunctor n).obj P ⟶ Q, f = 0 := by
    intro f
    apply Karoubi.hom_ext
    funext i j
    have hs : Subsingleton ((baseShift n).obj (P.X.X i) ⟶ Q.X.X j) := by
      rw [baseShift_obj]
      refine ⟨fun a b => ?_⟩
      have hz : ∀ a : (⟨⟨⟨(P.X.X i).obj.obj.par,
          ⟨(P.X.X i).obj.obj.obj.shift + n, (P.X.X i).obj.obj.obj.obj⟩⟩⟩⟩ : ShiftBase k C) ⟶
          Q.X.X j, a = 0 := by
        intro a
        apply Subtype.ext
        apply Subtype.ext
        have hf := a.val.property
        change a.val.val ∈ degree (R := k)
          (P.X.X i).obj.obj.obj.obj (Q.X.X j).obj.obj.obj.obj
          (0 + (((P.X.X i).obj.obj.obj.shift + n) - (Q.X.X j).obj.obj.obj.shift)) at hf
        have hb := hB (Set.mem_range_self (i, j))
        dsimp [bounds] at hb
        rw [hN _ _ _ (by omega)] at hf
        exact hf
      rw [hz a, hz b]
    exact hs.elim _ _
  rw [zero f, zero g]

/-- Laurentian Homs of the original category imply the categorical shift bound
on every indecomposable of its graded additive Karoubi envelope. -/
theorem shiftHomBoundedBelow [DegreeHomFinite (k := k) (C := C)]
    (h : HomBoundedBelow (k := k) (C := C)) :
    KrullSchmidt.ShiftHomBoundedBelow k (C := GSKar k C) := by
  intro i
  obtain ⟨N, hN⟩ := shift_hom_boundedBelow h i.rep i.rep
  refine ⟨N, fun n hn => ?_⟩
  have heq : K₀.mk ((shiftFunctor n).obj i.rep) =
      K₀.mk (KrullSchmidt.indecShift k n i).rep := by
    rw [← int_T_smul_mk]
    exact KrullSchmidt.int_T_smul_indec k n i
  obtain ⟨e⟩ := (KrullSchmidt.mk_eq_mk_iff k).1 heq
  let := hN n hn
  exact ⟨fun f g => (cancel_epi e.hom).1 (Subsingleton.elim _ _)⟩

/-- The Laurentian envelope theorem used by BE2 Theorems 11.3 and 11.7:
`K₀` is free over `ℤ[q,q⁻¹]`, with basis the integer-shift orbits of
indecomposables. Parity shifts have not been identified. -/
theorem k0_free_laurentInt [DegreeHomFinite (k := k) (C := C)]
    (h : HomBoundedBelow (k := k) (C := C)) :
    letI := K₀.moduleLaurentInt k (GSKar k C)
    Module.Free (LaurentPolynomial ℤ) (K₀ (GSKar k C)) :=
  KrullSchmidt.k0_free_laurentInt k (shiftHomBoundedBelow h)

end StringDiagrams.GSKar

namespace StringDiagrams.GSKarAlg
variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The Laurentian superalgebra form of BE2 §11's corrected preliminary fact.
The target is the graded additive Karoubi envelope; identification with graded
left projectives is a separate comparison. No finite total dimension is assumed. -/
theorem k0_free_laurentInt (𝒢 : GradedSuperalgebra k A)
    (hfin : ∀ n : ℤ, FiniteDimensional k (𝒢.degree n))
    (hbelow : ∃ N : ℤ, ∀ n < N, 𝒢.degree n = ⊥) :
    letI := K₀.moduleLaurentInt k (GSKar k (SuperalgebraCat 𝒢.parity))
    Module.Free (LaurentPolynomial ℤ) (K₀ (GSKar k (SuperalgebraCat 𝒢.parity))) := by
  let : GSKar.DegreeHomFinite (k := k) (C := SuperalgebraCat 𝒢.parity) :=
    ⟨fun _ _ n => hfin n⟩
  exact GSKar.k0_free_laurentInt (fun _ _ => hbelow)

end StringDiagrams.GSKarAlg
