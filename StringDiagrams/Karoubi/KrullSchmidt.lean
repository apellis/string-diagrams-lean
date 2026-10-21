/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Algebra.FiniteDimensionalLocal
import StringDiagrams.Super.K0
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel

/-!
# Hom-finite Krull–Schmidt and the integral basis of split K₀

The parity-independent part of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §11 (first preliminary fact, an input to Theorem 11.3):
in an idempotent-complete Hom-finite linear category, indecomposable isomorphism
classes form an integral basis of the existing `StringDiagrams.K₀`.

The algebraic input is Fitting's lemma. Decomposition is proved by induction on
endomorphism dimension; radical-quotient dimensions separate indecomposables.
Neither a decomposition nor a basis is assumed. This does not assert freeness over
the covering coefficient ring: parity-fixed indecomposables obstruct that assertion.
-/

noncomputable section

namespace StringDiagrams.KrullSchmidt

open CategoryTheory CategoryTheory.Limits Module

universe v u

/-- A `k`-linear category is **Hom-finite** if all its Hom-spaces are finite-dimensional. -/
class HomFinite (k : Type*) [Field k] (𝒞 : Type u) [Category.{v} 𝒞] [Preadditive 𝒞]
    [Linear k 𝒞] : Prop where
  finiteDimensional : ∀ X Y : 𝒞, FiniteDimensional k (X ⟶ Y)

attribute [instance] HomFinite.finiteDimensional

variable {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞]

/-- An object is **indecomposable** if it is nonzero and its only idempotent endomorphisms are
`0` and `1`. -/
def IsIndec (X : 𝒞) : Prop := ¬ IsZero X ∧ ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X

/-- A fully faithful additive functor preserves and reflects indecomposability. -/
theorem isIndec_obj_iff {D : Type*} [Category D] [Preadditive D]
    (F : 𝒞 ⥤ D) [F.Full] [F.Faithful] [F.Additive] (X : 𝒞) :
    IsIndec (F.obj X) ↔ IsIndec X := by
  have hz : IsZero (F.obj X) ↔ IsZero X := by
    simp only [IsZero.iff_id_eq_zero, ← F.map_id X, ← F.map_zero (X := X) (Y := X),
      F.map_injective.eq_iff]
  constructor
  · rintro ⟨h0, hi⟩
    refine ⟨fun h => h0 (hz.2 h), fun e he => ?_⟩
    rcases hi (F.map e) (by rw [← F.map_comp, he]) with h | h
    · exact Or.inl (F.map_injective (by simpa using h))
    · exact Or.inr (F.map_injective (by simpa using h))
  · rintro ⟨h0, hi⟩
    refine ⟨fun h => h0 (hz.1 h), fun e he => ?_⟩
    have hp : F.preimage e ≫ F.preimage e = F.preimage e := by
      apply F.map_injective
      simpa using he
    rcases hi (F.preimage e) hp with h | h
    · left
      simpa using congrArg F.map h
    · right
      simpa using congrArg F.map h

/-! ## Splitting idempotents -/

section Split

variable [HasBinaryBiproducts 𝒞]

/-- The isomorphism `X ≅ Y ⊞ Z` given by a complete family of orthogonal retractions. -/
@[simps]
def isoOfData {X Y Z : 𝒞} (i : Y ⟶ X) (p : X ⟶ Y) (i' : Z ⟶ X) (p' : X ⟶ Z)
    (h₁ : i ≫ p = 𝟙 Y) (h₂ : i' ≫ p' = 𝟙 Z) (h₃ : i ≫ p' = 0) (h₄ : i' ≫ p = 0)
    (h₅ : p ≫ i + p' ≫ i' = 𝟙 X) : X ≅ Y ⊞ Z where
  hom := biprod.lift p p'
  inv := biprod.desc i i'
  hom_inv_id := by rw [biprod.lift_desc, h₅]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [h₁, h₂, h₃, h₄]

omit [HasBinaryBiproducts 𝒞] in
theorem idem_one_sub {X : 𝒞} {e : X ⟶ X} (he : e ≫ e = e) : (𝟙 X - e) ≫ (𝟙 X - e) = 𝟙 X - e := by
  simp [Preadditive.sub_comp, Preadditive.comp_sub, he]

omit [HasBinaryBiproducts 𝒞] in
/-- **Splitting an idempotent** in an idempotent complete category: `X ≅ im e ⊞ im (1 - e)`. -/
theorem exists_split [IsIdempotentComplete 𝒞] {X : 𝒞} (e : X ⟶ X) (he : e ≫ e = e) :
    ∃ (Y Z : 𝒞) (i : Y ⟶ X) (p : X ⟶ Y) (i' : Z ⟶ X) (p' : X ⟶ Z), i ≫ p = 𝟙 Y ∧
      i' ≫ p' = 𝟙 Z ∧ i ≫ p' = 0 ∧ i' ≫ p = 0 ∧ p ≫ i = e ∧ p' ≫ i' = 𝟙 X - e := by
  obtain ⟨Y, i, p, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split X e he
  obtain ⟨Z, i', p', h₁', h₂'⟩ :=
    IsIdempotentComplete.idempotents_split X (𝟙 X - e) (idem_one_sub he)
  have hi : i = i ≫ e := by rw [← h₂, ← Category.assoc, h₁, Category.id_comp]
  have hp' : p' = (𝟙 X - e) ≫ p' := by rw [← h₂', Category.assoc, h₁', Category.comp_id]
  have hi' : i' = i' ≫ (𝟙 X - e) := by rw [← h₂', ← Category.assoc, h₁', Category.id_comp]
  have hp : p = e ≫ p := by rw [← h₂, Category.assoc, h₁, Category.comp_id]
  refine ⟨Y, Z, i, p, i', p', h₁, h₁', ?_, ?_, h₂, h₂'⟩
  · rw [hi, hp', Category.assoc, ← Category.assoc e]
    simp [Preadditive.comp_sub, he]
  · rw [hi', hp, Category.assoc, ← Category.assoc (𝟙 X - e)]
    simp [Preadditive.sub_comp, he]

/-- An indecomposable object does not split into two nonzero summands. -/
theorem IsIndec.isZero_or_isZero {X Y Z : 𝒞} (hX : IsIndec X) (φ : X ≅ Y ⊞ Z) :
    IsZero Y ∨ IsZero Z := by
  set e := φ.hom ≫ biprod.fst ≫ biprod.inl ≫ φ.inv
  have he : e ≫ e = e := by simp [e]
  rcases hX.2 e he with h | h
  · left
    rw [IsZero.iff_id_eq_zero]
    have : biprod.inl ≫ φ.inv ≫ e ≫ φ.hom ≫ biprod.fst = 𝟙 Y := by simp [e]
    rw [← this, h]; simp
  · right
    rw [IsZero.iff_id_eq_zero]
    have : biprod.inr ≫ φ.inv ≫ (𝟙 X - e) ≫ φ.hom ≫ biprod.snd = 𝟙 Z := by
      simp [e, Preadditive.sub_comp]
    rw [← this, h, sub_self]; simp

/-- **Indecomposability via biproducts** (idempotent complete categories). -/
theorem isIndec_iff [IsIdempotentComplete 𝒞] {X : 𝒞} :
    IsIndec X ↔ ¬ IsZero X ∧ ∀ Y Z : 𝒞, Nonempty (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z := by
  refine ⟨fun h => ⟨h.1, fun Y Z ⟨φ⟩ => h.isZero_or_isZero φ⟩, fun ⟨h0, h⟩ => ⟨h0, fun e he => ?_⟩⟩
  obtain ⟨Y, Z, i, p, i', p', h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_split e he
  rcases h Y Z ⟨isoOfData i p i' p' h₁ h₂ h₃ h₄ (by rw [h₅, h₆, add_sub_cancel])⟩ with hY | hZ
  · left; rw [← h₅, hY.eq_of_src i, Limits.comp_zero]
  · right
    have : 𝟙 X - e = 0 := by rw [← h₆, hZ.eq_of_src i', Limits.comp_zero]
    exact (sub_eq_zero.1 this).symm

end Split

/-- In an idempotent-complete additive category, the idempotent formulation is
Mathlib's biproduct formulation of indecomposability. -/
theorem isIndec_iff_indecomposable [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] (X : 𝒞) :
    IsIndec X ↔ CategoryTheory.Indecomposable X := by
  rw [isIndec_iff, CategoryTheory.Indecomposable]
  exact and_congr_right fun _ => ⟨fun h Y Z e => h Y Z ⟨e⟩,
    fun h Y Z ⟨e⟩ => h Y Z e⟩

section K0
variable [HasBinaryBiproducts 𝒞]

theorem mk_eq_add_of_iso {X Y Z : 𝒞} (e : X ≅ Y ⊞ Z) :
    K₀.mk X = K₀.mk Y + K₀.mk Z :=
  (K₀.mk_eq_mk_of_iso e).trans (K₀.mk_biprod Y Z)

theorem mk_isZero {X : 𝒞} (hX : IsZero X) : K₀.mk X = 0 := by
  have hXX : IsZero (X ⊞ X) := by
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext <;> exact hX.eq_of_tgt _ _
  have h := K₀.mk_biprod X X
  rw [K₀.mk_eq_mk_of_iso (hXX.iso hX)] at h
  exact left_eq_add.mp h
end K0

/-! ## Existence of decompositions -/

section Existence

variable (k : Type*) [Field k] [Linear k 𝒞] [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞]
  [IsIdempotentComplete 𝒞]

omit [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
theorem finrank_end_pos {X : 𝒞} (hX : ¬ IsZero X) : 0 < finrank k (X ⟶ X) := by
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨𝟙 X, fun h => hX ?_⟩
  rwa [IsZero.iff_id_eq_zero]

omit [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
/-- A proper summand has a smaller endomorphism algebra. -/
theorem finrank_end_lt {X Y Z : 𝒞} (i : Y ⟶ X) (p : X ⟶ Y) (i' : Z ⟶ X) (p' : X ⟶ Z)
    (h₁ : i ≫ p = 𝟙 Y) (h₂ : i' ≫ p' = 𝟙 Z) (h₃ : i ≫ p' = 0) (h₄ : i' ≫ p = 0)
    (hZ : ¬ IsZero Z) : finrank k (Y ⟶ Y) < finrank k (X ⟶ X) := by
  let Φ : ((Y ⟶ Y) × (Z ⟶ Z)) →ₗ[k] (X ⟶ X) :=
    (Linear.leftComp k X p ∘ₗ Linear.rightComp k Y i) ∘ₗ LinearMap.fst k _ _ +
      (Linear.leftComp k X p' ∘ₗ Linear.rightComp k Z i') ∘ₗ LinearMap.snd k _ _
  have hΦ' : ∀ fg, Φ fg = p ≫ fg.1 ≫ i + p' ≫ fg.2 ≫ i' := fun fg => rfl
  have hΦ : Function.Injective Φ := by
    intro a b hab
    rw [hΦ', hΦ'] at hab
    have e₁ := congrArg (fun g => i ≫ g ≫ p) hab
    have e₂ := congrArg (fun g => i' ≫ g ≫ p') hab
    simp only [Preadditive.add_comp,
      Category.assoc, reassoc_of% h₁, reassoc_of% h₂, h₁, h₂, h₃,
      h₄, Limits.comp_zero, add_zero, zero_add, Category.comp_id] at e₁ e₂
    exact Prod.ext e₁ e₂
  have := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_prod] at this
  have := finrank_end_pos k hZ
  omega

include k in
/-- **Existence of Krull–Schmidt decompositions**: the class of every object is a sum of
classes of indecomposable objects. -/
theorem of_mem_closure_indec (X : 𝒞) :
    K₀.mk X ∈ AddSubmonoid.closure {x | ∃ Z : 𝒞, IsIndec Z ∧ x = K₀.mk Z} := by
  induction h : finrank k (X ⟶ X) using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases h0 : IsZero X
    · rw [mk_isZero h0]; exact AddSubmonoid.zero_mem _
    by_cases hi : IsIndec X
    · exact AddSubmonoid.subset_closure ⟨X, hi, rfl⟩
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
    rw [mk_eq_add_of_iso (isoOfData i p i' p' h₁ h₂ h₃ h₄
      (by rw [h₅, h₆, add_sub_cancel]))]
    refine AddSubmonoid.add_mem _ (ih _ ?_ Y rfl) (ih _ ?_ Z rfl)
    · rw [← h]; exact finrank_end_lt k i p i' p' h₁ h₂ h₃ h₄ hZ
    · rw [← h]; exact finrank_end_lt k i' p' i p h₂ h₁ h₄ h₃ hY

end Existence

/-! ## Local endomorphism rings and the multiplicity functionals -/

section Mult

variable (k : Type*) [Field k] [Linear k 𝒞] [HomFinite k 𝒞]

include k in
/-- **Fitting's lemma**: an endomorphism of an indecomposable object is nilpotent or invertible. -/
theorem IsIndec.isNilpotent_or_isUnit {X : 𝒞} (hX : IsIndec X) (f : End X) :
    IsNilpotent f ∨ IsUnit f := by
  have : FiniteDimensional k (End X) := HomFinite.finiteDimensional X X
  refine FiniteDimensionalAlgebra.isNilpotent_or_isUnit_of_idempotent k (fun e he => ?_) f
  have he' : e ≫ e = e := by rw [← End.mul_def]; exact he.eq
  rcases hX.2 e he' with h | h
  · exact Or.inl h
  · exact Or.inr h

omit [HomFinite k 𝒞] [Linear k 𝒞] in
theorem IsIndec.nontrivial {X : 𝒞} (hX : IsIndec X) : Nontrivial (End X) :=
  ⟨⟨0, 1, fun h => hX.1 ((IsZero.iff_id_eq_zero _).2 h.symm)⟩⟩

include k in
/-- **The endomorphism ring of an indecomposable object is local.** -/
theorem IsIndec.isLocalRing {X : 𝒞} (hX : IsIndec X) : IsLocalRing (End X) :=
  have := hX.nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (hX.isNilpotent_or_isUnit k a).elim (fun h => Or.inr h.isUnit_one_sub) Or.inl

omit [HomFinite k 𝒞] [Linear k 𝒞] in
/-- In a (possibly noncommutative) local ring, a sum of nonunits is a nonunit. -/
theorem nonunits_add' {R : Type*} [Ring R] [IsLocalRing R] {a b : R} (ha : ¬ IsUnit a)
    (hb : ¬ IsUnit b) : ¬ IsUnit (a + b) := by
  rintro ⟨u, hu⟩
  have h : (↑u⁻¹ * a) + (↑u⁻¹ * b) = 1 := by rw [← mul_add, ← hu, Units.inv_mul]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h' | h'
  · exact ha ((Units.isUnit_units_mul u⁻¹ a).1 h')
  · exact hb ((Units.isUnit_units_mul u⁻¹ b).1 h')

/-- The radical `rad(Z, X)`: the morphisms `f : Z → X` such that `f ≫ g` is never invertible. -/
def rad {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) : Submodule k (Z ⟶ X) where
  carrier := {f | ∀ g : X ⟶ Z, ¬ IsUnit (M := End Z) (f ≫ g)}
  zero_mem' g h := by
    have := hZ.nontrivial
    rw [Limits.zero_comp] at h
    exact not_isUnit_zero h
  add_mem' {f f'} hf hf' g := by
    have := hZ.isLocalRing k
    rw [Preadditive.add_comp]
    exact nonunits_add' (R := End Z) (hf g) (hf' g)
  smul_mem' c f hf g h := by
    rw [Linear.smul_comp] at h
    have hi : IsIso (c • (f ≫ g)) := (isUnit_iff_isIso (X := Z) _).1 h
    refine hf g ⟨⟨f ≫ g, c • inv (c • (f ≫ g)), ?_, ?_⟩, rfl⟩
    · rw [End.mul_def, Linear.smul_comp, ← Linear.comp_smul, IsIso.inv_hom_id]; rfl
    · rw [End.mul_def, Linear.comp_smul, ← Linear.smul_comp, IsIso.hom_inv_id]; rfl

variable {k}

theorem mem_rad {Z X : 𝒞} {hZ : IsIndec Z} {f : Z ⟶ X} :
    f ∈ rad k hZ X ↔ ∀ g : X ⟶ Z, ¬ IsUnit (M := End Z) (f ≫ g) := Iff.rfl

variable (k)

/-- Postcomposition with an isomorphism. -/
@[simps]
def postIso (Z : 𝒞) {X X' : 𝒞} (φ : X ≅ X') : (Z ⟶ X) ≃ₗ[k] (Z ⟶ X') where
  toFun f := f ≫ φ.hom
  invFun f := f ≫ φ.inv
  map_add' := by simp
  map_smul' := by simp
  left_inv f := by simp
  right_inv f := by simp

theorem rad_map_postIso {Z : 𝒞} (hZ : IsIndec Z) {X X' : 𝒞} (φ : X ≅ X') :
    (rad k hZ X).map (postIso k Z φ).toLinearMap = rad k hZ X' := by
  ext f
  constructor
  · rintro ⟨f₀, hf₀, rfl⟩ g
    simpa using hf₀ (φ.hom ≫ g)
  · intro hf
    refine ⟨f ≫ φ.inv, fun g => ?_, by simp⟩
    simpa using hf (φ.inv ≫ g)

/-- The multiplicity invariant `dim Hom(Z, X) - dim rad(Z, X)`. -/
def mult {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) : ℤ :=
  (finrank k (Z ⟶ X) : ℤ) - finrank k (rad k hZ X)

theorem mult_iso {Z : 𝒞} (hZ : IsIndec Z) {X X' : 𝒞} (φ : X ≅ X') :
    mult k hZ X = mult k hZ X' := by
  unfold mult
  rw [(postIso k Z φ).finrank_eq, ← rad_map_postIso k hZ φ, LinearEquiv.finrank_map_eq]

theorem finrank_submodule_prod {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] [FiniteDimensional k M] [FiniteDimensional k N] (p : Submodule k M)
    (q : Submodule k N) : finrank k (p.prod q) = finrank k p + finrank k q := by
  let e : p.prod q ≃ₗ[k] p × q :=
    { toFun := fun x => (⟨x.1.1, (Submodule.mem_prod.1 x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.1 x.2).2⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), Submodule.mem_prod.2 ⟨y.1.2, y.2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_prod]

variable [HasBinaryBiproducts 𝒞]

/-- `Hom(Z, X ⊞ Y) ≅ Hom(Z, X) × Hom(Z, Y)`. -/
@[simps]
def biprodEquiv (Z X Y : 𝒞) : (Z ⟶ X ⊞ Y) ≃ₗ[k] (Z ⟶ X) × (Z ⟶ Y) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  invFun ab := biprod.lift ab.1 ab.2
  map_add' f g := by simp
  map_smul' c f := by simp
  left_inv f := by apply biprod.hom_ext <;> simp
  right_inv ab := by simp

theorem rad_map_biprodEquiv {Z : 𝒞} (hZ : IsIndec Z) (X Y : 𝒞) :
    (rad k hZ (X ⊞ Y)).map (biprodEquiv k Z X Y).toLinearMap = (rad k hZ X).prod (rad k hZ Y) := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_map, Submodule.mem_prod, LinearEquiv.coe_coe, biprodEquiv_apply,
    Prod.mk.injEq]
  constructor
  · rintro ⟨f, hf, rfl, rfl⟩
    exact ⟨fun g => by simpa using hf (biprod.fst ≫ g), fun g => by simpa using hf (biprod.snd ≫ g)⟩
  · rintro ⟨ha, hb⟩
    refine ⟨biprod.lift a b, fun g => ?_, by simp, by simp⟩
    have := hZ.isLocalRing k
    rw [biprod.lift_eq, Preadditive.add_comp, Category.assoc, Category.assoc]
    exact nonunits_add' (R := End Z) (ha _) (hb _)

theorem mult_biprod {Z : 𝒞} (hZ : IsIndec Z) (X Y : 𝒞) :
    mult k hZ (X ⊞ Y) = mult k hZ X + mult k hZ Y := by
  unfold mult
  rw [(biprodEquiv k Z X Y).finrank_eq, Module.finrank_prod, ← LinearEquiv.finrank_map_eq
    (biprodEquiv k Z X Y), rad_map_biprodEquiv, finrank_submodule_prod]
  push_cast; ring

/-- **The multiplicity functional** `K₀(𝒞) → ℤ` of an indecomposable object `Z`. -/
def multK {Z : 𝒞} (hZ : IsIndec Z) : K₀ 𝒞 →+ ℤ :=
  K₀.lift (mult k hZ) (fun _ _ e => mult_iso k hZ e) (mult_biprod k hZ)

@[simp] theorem multK_of {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) :
    multK k hZ (K₀.mk X) = mult k hZ X := K₀.lift_mk _ _ _ _

theorem multK_self_pos {Z : 𝒞} (hZ : IsIndec Z) : 0 < multK k hZ (K₀.mk Z) := by
  rw [multK_of, mult, sub_pos, Nat.cast_lt]
  refine Submodule.finrank_lt fun h => ?_
  have : 𝟙 Z ∈ rad k hZ Z := h ▸ Submodule.mem_top
  exact this (𝟙 Z) (by rw [Category.comp_id]; exact isUnit_one)

/-- **Uniqueness part of Krull–Schmidt**: the multiplicity functional of `Z` vanishes on the
indecomposables not isomorphic to `Z`. -/
theorem multK_of_not_iso {Z Z' : 𝒞} (hZ : IsIndec Z) (hZ' : IsIndec Z')
    (h : ¬ Nonempty (Z ≅ Z')) : multK k hZ (K₀.mk Z') = 0 := by
  have htop : rad k hZ Z' = ⊤ := by
    refine eq_top_iff.2 fun f _ g hfg => h ?_
    obtain ⟨u, hu⟩ := hfg
    have hv : f ≫ g ≫ (↑u⁻¹ : End Z) = 𝟙 Z := by
      have := u.inv_mul
      rw [End.mul_def, hu] at this
      rw [← Category.assoc]; exact this
    set g' : Z' ⟶ Z := g ≫ (↑u⁻¹ : End Z)
    have he : (g' ≫ f) ≫ (g' ≫ f) = g' ≫ f := by
      rw [Category.assoc, ← Category.assoc f, hv, Category.id_comp]
    rcases hZ'.2 _ he with h0 | h1
    · exfalso
      apply hZ.1
      rw [IsZero.iff_id_eq_zero]
      calc 𝟙 Z = (f ≫ g') ≫ (f ≫ g') := by rw [hv, Category.id_comp]
        _ = f ≫ (g' ≫ f) ≫ g' := by simp only [Category.assoc]
        _ = 0 := by rw [h0]; simp
    · exact ⟨⟨f, g', hv, h1⟩⟩
  rw [multK_of, mult, htop, finrank_top, sub_self]

end Mult


/-! ## The integral basis -/

variable (𝒞) in
/-- Indecomposable objects modulo isomorphism, without identifying parity shifts. -/
def indecSetoid : Setoid {X : 𝒞 // IsIndec X} where
  r X Y := Nonempty (X.1 ≅ Y.1)
  iseqv := ⟨fun X => ⟨Iso.refl X.1⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

variable (𝒞) in
/-- Isomorphism classes of nonzero indecomposable objects. -/
def IndecClass := Quotient (indecSetoid 𝒞)

/-- A representative of an indecomposable isomorphism class. -/
def IndecClass.rep (b : IndecClass 𝒞) : 𝒞 := (Quotient.out b).1

theorem IndecClass.isIndec_rep (b : IndecClass 𝒞) : IsIndec b.rep := (Quotient.out b).2

theorem IndecClass.eq_of_iso {b b' : IndecClass 𝒞} (e : b.rep ≅ b'.rep) : b = b' := by
  rw [← Quotient.out_eq b, ← Quotient.out_eq b']
  exact Quotient.sound ⟨e⟩

theorem IndecClass.exists_iso_rep {X : 𝒞} (hX : IsIndec X) :
    Nonempty (X ≅ IndecClass.rep (Quotient.mk (indecSetoid 𝒞) ⟨X, hX⟩)) := by
  obtain ⟨e⟩ := Quotient.mk_out (s := indecSetoid 𝒞) ⟨X, hX⟩
  exact ⟨e.symm⟩

section Basis
variable (k : Type*) [Field k] [Linear k 𝒞] [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞]
include k

/-- Distinct indecomposable classes are integrally linearly independent. -/
theorem linearIndependent_indec :
    LinearIndependent ℤ (fun b : IndecClass 𝒞 => K₀.mk b.rep) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg b₀ hb₀
  have key := congrArg (multK k b₀.isIndec_rep) hg
  rw [map_sum, map_zero] at key
  simp only [map_zsmul, zsmul_eq_mul] at key
  rw [Finset.sum_eq_single b₀] at key
  · exact (mul_eq_zero.1 key).resolve_right (ne_of_gt (multK_self_pos k b₀.isIndec_rep))
  · intro b _ hb
    rw [multK_of_not_iso k b₀.isIndec_rep b.isIndec_rep
      (fun ⟨e⟩ => hb (IndecClass.eq_of_iso e).symm), mul_zero]
  · exact fun h => (h hb₀).elim

variable [IsIdempotentComplete 𝒞]

/-- Every object class is in the integral span of the indecomposables. -/
theorem mk_mem_span (X : 𝒞) :
    K₀.mk X ∈ Submodule.span ℤ (Set.range fun b : IndecClass 𝒞 => K₀.mk b.rep) := by
  have h := of_mem_closure_indec k X
  refine (AddSubmonoid.closure_le (S := (Submodule.span ℤ
    (Set.range fun b : IndecClass 𝒞 => K₀.mk b.rep)).toAddSubmonoid)).2 ?_ h
  rintro _ ⟨Z, hZ, rfl⟩
  obtain ⟨e⟩ := IndecClass.exists_iso_rep hZ
  change K₀.mk Z ∈ Submodule.span _ _
  rw [K₀.mk_eq_mk_of_iso e]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem mem_span_indec (x : K₀ 𝒞) :
    x ∈ Submodule.span ℤ (Set.range fun b : IndecClass 𝒞 => K₀.mk b.rep) := by
  induction x using K₀.induction_on with
  | mk X => exact mk_mem_span k X
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | neg x hx => exact Submodule.neg_mem _ hx

/-- The integral Krull–Schmidt basis of the split Grothendieck group.
This proves the parity-independent basis assertion in BE2 §11, used in Theorem 11.3,
for any Hom-finite idempotent-complete linear category. It does not identify parity
or grading shifts, and does not claim freeness over `Zπ` or its Laurent extension. -/
def indecBasis : Basis (IndecClass 𝒞) ℤ (K₀ 𝒞) :=
  Basis.mk (linearIndependent_indec k) fun x _ => mem_span_indec k x

@[simp] theorem indecBasis_apply (b : IndecClass 𝒞) : indecBasis k b = K₀.mk b.rep := by
  simp [indecBasis]

/-- Split K₀ of a Hom-finite idempotent-complete linear category is free over ℤ. -/
theorem free : Module.Free ℤ (K₀ 𝒞) := Module.Free.of_basis (indecBasis k)

end Basis
end StringDiagrams.KrullSchmidt
