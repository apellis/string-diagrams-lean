/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Karoubi.KrullSchmidt

/-!
# Object-level Krull–Schmidt decompositions

The categorical Krull–Schmidt input to Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, §11 (used in Theorem 11.3).
Every object in a Hom-finite idempotent-complete additive category is a finite
biproduct of indecomposables, uniquely up to permutation and isomorphism.
Consequently equality of object classes in the existing split `K₀` detects
isomorphism, and binary biproducts satisfy cancellation.
-/

noncomputable section
namespace StringDiagrams.KrullSchmidt
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open scoped ZeroObject

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C] [HasZeroObject C]

/-- The finite iterated biproduct of chosen indecomposable representatives. -/
def sumList : List (IndecClass C) → C
  | [] => 0
  | b :: l => b.rep ⊞ sumList l

/-- Concatenation corresponds to binary biproduct. -/
def sumListAppendIso : (l₁ l₂ : List (IndecClass C)) →
    sumList (l₁ ++ l₂) ≅ sumList l₁ ⊞ sumList l₂
  | [], _ => isoZeroBiprod (isZero_zero C)
  | b :: l₁, l₂ => biprod.mapIso (Iso.refl b.rep) (sumListAppendIso l₁ l₂) ≪≫
      (biprod.associator _ _ _).symm

/-- Reordering summands does not change the isomorphism class. -/
theorem nonempty_iso_sumList_of_perm {l l' : List (IndecClass C)} (h : l.Perm l') :
    Nonempty (sumList l ≅ sumList l') := by
  induction h with
  | nil => exact ⟨Iso.refl _⟩
  | cons b _ ih => exact ⟨biprod.mapIso (Iso.refl b.rep) ih.some⟩
  | swap a b l =>
    exact ⟨(biprod.associator _ _ _).symm ≪≫
      biprod.mapIso (biprod.braiding _ _) (Iso.refl _) ≪≫ biprod.associator _ _ _⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.some ≪≫ ih₂.some⟩

variable (k : Type*) [Field k] [Linear k C] [HomFinite k C] [IsIdempotentComplete C]
include k

/-- Existence of finite decompositions of objects, not merely decompositions of K₀ classes. -/
theorem exists_iso_sumList (X : C) :
    ∃ l : List (IndecClass C), Nonempty (X ≅ sumList l) := by
  induction h : Module.finrank k (X ⟶ X) using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases h0 : IsZero X
    · exact ⟨[], ⟨h0.iso (isZero_zero C)⟩⟩
    by_cases hi : IsIndec X
    · obtain ⟨e⟩ := IndecClass.exists_iso_rep hi
      exact ⟨[Quotient.mk (indecSetoid C) ⟨X, hi⟩],
        ⟨e ≪≫ isoBiprodZero (isZero_zero C)⟩⟩
    obtain ⟨e, he, he0, he1⟩ : ∃ e : X ⟶ X, e ≫ e = e ∧ e ≠ 0 ∧ e ≠ 𝟙 X := by
      by_contra hne
      push Not at hne
      exact hi ⟨h0, fun e he => by
        by_cases h' : e = 0
        · exact Or.inl h'
        · exact Or.inr (hne e he h')⟩
    obtain ⟨Y, Z, i, p, i', p', h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_split e he
    have hY : ¬ IsZero Y := fun hY => he0 (by rw [← h₅, hY.eq_of_src i, Limits.comp_zero])
    have hZ : ¬ IsZero Z := fun hZ => he1 (by
      have : 𝟙 X - e = 0 := by rw [← h₆, hZ.eq_of_src i', Limits.comp_zero]
      exact (sub_eq_zero.1 this).symm)
    obtain ⟨l, ⟨el⟩⟩ := ih _ (by rw [← h]; exact finrank_end_lt k i p i' p' h₁ h₂ h₃ h₄ hZ) Y rfl
    obtain ⟨m, ⟨em⟩⟩ := ih _ (by rw [← h]; exact finrank_end_lt k i' p' i p h₂ h₁ h₄ h₃ hY) Z rfl
    exact ⟨l ++ m, ⟨isoOfData i p i' p' h₁ h₂ h₃ h₄ (by rw [h₅, h₆, add_sub_cancel]) ≪≫
      biprod.mapIso el em ≪≫ (sumListAppendIso l m).symm⟩⟩

/-- Basis coordinates count summands with their integral multiplicities. -/
theorem repr_mk_sumList [DecidableEq (IndecClass C)] (l : List (IndecClass C))
    (b : IndecClass C) : (indecBasis k).repr (K₀.mk (sumList l)) b = l.count b := by
  induction l with
  | nil => simp [sumList, K₀.mk_zero]
  | cons a l ih =>
    rw [sumList, K₀.mk_biprod, map_add, Finsupp.add_apply, ← indecBasis_apply k a,
      Module.Basis.repr_self, Finsupp.single_apply, ih, List.count_cons]
    by_cases h : a = b
    · subst h; simp [add_comm]
    · simp [h]

/-- Equal K₀ classes of decompositions have the same summands, with multiplicity. -/
theorem perm_of_mk_sumList_eq {l l' : List (IndecClass C)}
    (h : K₀.mk (sumList l) = K₀.mk (sumList l')) : l.Perm l' := by
  classical
  rw [List.perm_iff_count]
  intro b
  have := congrArg (fun x => (indecBasis k).repr x b) h
  simp only [repr_mk_sumList] at this
  simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using Int.natCast_inj.mp this

/-- Uniqueness of Krull–Schmidt decompositions up to permutation and isomorphism. -/
theorem nonempty_iso_sumList_iff {l l' : List (IndecClass C)} :
    Nonempty (sumList l ≅ sumList l') ↔ l.Perm l' :=
  ⟨fun ⟨e⟩ => perm_of_mk_sumList_eq k (K₀.mk_eq_mk_of_iso e), nonempty_iso_sumList_of_perm⟩

/-- For objects in this category, split K₀ detects isomorphism. -/
theorem mk_eq_mk_iff {X Y : C} : K₀.mk X = K₀.mk Y ↔ Nonempty (X ≅ Y) := by
  refine ⟨fun h => ?_, fun ⟨e⟩ => K₀.mk_eq_mk_of_iso e⟩
  obtain ⟨l, ⟨e⟩⟩ := exists_iso_sumList k X
  obtain ⟨m, ⟨f⟩⟩ := exists_iso_sumList k Y
  have hp : l.Perm m := perm_of_mk_sumList_eq k
    (by rw [← K₀.mk_eq_mk_of_iso e, ← K₀.mk_eq_mk_of_iso f, h])
  exact ⟨e ≪≫ (nonempty_iso_sumList_of_perm hp).some ≪≫ f.symm⟩

/-- Cancellation of a common summand. -/
theorem cancel_biprod {X Y Z : C} (e : X ⊞ Z ≅ Y ⊞ Z) : Nonempty (X ≅ Y) := by
  apply (mk_eq_mk_iff k).1
  have h := K₀.mk_eq_mk_of_iso e
  simpa only [K₀.mk_biprod, add_left_inj] using h

end StringDiagrams.KrullSchmidt
