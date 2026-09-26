import StringDiagrams.Biadjunction.Trace
import StringDiagrams.Biadjunction.Linear
import Mathlib.CategoryTheory.Bicategory.SingleObj
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Biadjunctions in monoidal categories

A monoidal category `C` is a bicategory with one object, `MonoidalSingleObj C` (Mathlib), whose
1-morphisms are the objects of `C` (composition is `⊗`) and whose 2-morphisms are the
morphisms of `C`; whiskering, associators and unitors are those of `C`, definitionally. Under
this identification an exact pairing `ExactPairing X Y` (coevaluation `𝟙_ C ⟶ X ⊗ Y`,
evaluation `Y ⊗ X ⟶ 𝟙_ C`) is the same as a bicategorical adjunction `X ⊣ Y`
(`MonoidalDuality.adjunction`, `MonoidalDuality.exactPairing`), and a biduality (exact pairings
`X Y` and `Y X`) is a biadjunction (`MonoidalDuality.biadjunction`).

This file states the monoidal versions of the definitions and main results of
`StringDiagrams.Biadjunction`, obtained by transfer:

* `MonoidalDuality.rightMate Y Y' f`, `MonoidalDuality.leftMate Y Y' f : Y' ⟶ Y` for
  `f : X ⟶ X'`; they agree with Mathlib's `rightAdjointMate` and `leftAdjointMate` for the
  chosen right and left duals (`rightMate_eq_rightAdjointMate`,
  `leftMate_eq_leftAdjointMate`);
* `MonoidalDuality.IsCyclic Y Y' f`, closed under composition (`IsCyclic.comp`), and, in a
  preadditive (resp. linear) monoidal category, under sums (resp. scalar multiples);
* traces `MonoidalDuality.rightTrace Y f = η_ X Y ≫ f ▷ Y ≫ ε_ Y X` and
  `MonoidalDuality.leftTrace Y f = η_ Y X ≫ Y ◁ f ≫ ε_ X Y` in `End (𝟙_ C)`, with the
  cyclicity `rightTrace Y (f ≫ g) = rightTrace Y' (g ≫ f)` when `f` or `g` is cyclic, the
  relation of traces with mates, and additivity/linearity.
-/

namespace StringDiagrams

open CategoryTheory MonoidalCategory Bicategory

universe w v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- `leftZigzag` with its coherence isomorphism made explicit. -/
theorem leftZigzag_eq {B : Type*} [Bicategory B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
    leftZigzag η ε = η ▷ f ≫ (α_ f g f).hom ≫ f ◁ ε := by
  bicategory

/-- `rightZigzag` with its coherence isomorphism made explicit. -/
theorem rightZigzag_eq {B : Type*} [Bicategory B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
    rightZigzag η ε = g ◁ η ≫ (α_ g f g).inv ≫ ε ▷ g := by
  bicategory

namespace MonoidalDuality

/-- The one-object bicategory `MonoidalSingleObj C`, with its universe fixed. -/
abbrev SingleObj (C : Type u) [Category.{v} C] [MonoidalCategory C] : Type :=
  MonoidalSingleObj.{u, v, 1} C

/-- The unique object of the bicategory `MonoidalSingleObj C`. -/
local notation "⋆" => (MonoidalSingleObj.star C : SingleObj C)

/-- An exact pairing of `X` and `Y` as an adjunction `X ⊣ Y` in the one-object bicategory
`MonoidalSingleObj C`. -/
def adjunction (X Y : C) [ExactPairing X Y] :
    @Bicategory.Adjunction (SingleObj C) _ ⋆ ⋆ X Y where
  unit := η_ X Y
  counit := ε_ X Y
  left_triangle := by
    rw [leftZigzag_eq]
    exact ExactPairing.evaluation_coevaluation X Y
  right_triangle := by
    rw [rightZigzag_eq]
    exact ExactPairing.coevaluation_evaluation X Y

@[simp]
theorem adjunction_unit (X Y : C) [ExactPairing X Y] : (adjunction X Y).unit = η_ X Y := rfl

@[simp]
theorem adjunction_counit (X Y : C) [ExactPairing X Y] : (adjunction X Y).counit = ε_ X Y :=
  rfl

/-- An adjunction `X ⊣ Y` in `MonoidalSingleObj C` as an exact pairing of `X` and `Y`. -/
def exactPairing {X Y : C} (adj : @Bicategory.Adjunction (SingleObj C) _ ⋆ ⋆ X Y) :
    ExactPairing X Y where
  coevaluation' := adj.unit
  evaluation' := adj.counit
  coevaluation_evaluation' := by
    have h := adj.right_triangle
    rw [rightZigzag_eq] at h
    exact h
  evaluation_coevaluation' := by
    have h := adj.left_triangle
    rw [leftZigzag_eq] at h
    exact h

/-- A biduality (exact pairings of `X` with `Y` and of `Y` with `X`) as a biadjunction in
`MonoidalSingleObj C`. -/
def biadjunction (X Y : C) [ExactPairing X Y] [ExactPairing Y X] :
    @Biadjunction (SingleObj C) _ ⋆ ⋆ X Y where
  left := adjunction X Y
  right := adjunction Y X

theorem biadjunction_symm (X Y : C) [ExactPairing X Y] [ExactPairing Y X] :
    (biadjunction X Y).symm = biadjunction Y X := rfl

/-! ## Mates -/

section Mates

variable {X X' X'' : C} (Y Y' Y'' : C)

/-- The right mate `Y' ⟶ Y` of `f : X ⟶ X'`, for exact pairings `X Y` and `X' Y'`. -/
def rightMate [ExactPairing X Y] [ExactPairing X' Y'] (f : X ⟶ X') : Y' ⟶ Y :=
  Bicategory.conjugateEquiv (adjunction X' Y') (adjunction X Y) f

/-- The left mate `Y' ⟶ Y` of `f : X ⟶ X'`, for exact pairings `Y X` and `Y' X'`. -/
def leftMate [ExactPairing Y X] [ExactPairing Y' X'] (f : X ⟶ X') : Y' ⟶ Y :=
  (Bicategory.conjugateEquiv (adjunction Y X) (adjunction Y' X')).symm f

theorem rightMate_eq [ExactPairing X Y] [ExactPairing X' Y'] (f : X ⟶ X') :
    rightMate Y Y' f = (ρ_ Y').inv ≫ Y' ◁ η_ X Y ≫ Y' ◁ f ▷ Y ≫ (α_ Y' X' Y).inv ≫
      ε_ X' Y' ▷ Y ≫ (λ_ Y).hom := by
  have h := Bicategory.conjugateEquiv_apply' (adjunction X' Y') (adjunction X Y) f
  exact h

theorem leftMate_eq [ExactPairing Y X] [ExactPairing Y' X'] (f : X ⟶ X') :
    leftMate Y Y' f = (λ_ Y').inv ≫ η_ Y X ▷ Y' ≫ (α_ Y X Y').hom ≫ Y ◁ f ▷ Y' ≫
      Y ◁ ε_ Y' X' ≫ (ρ_ Y).hom := by
  have h := Bicategory.conjugateEquiv_symm_apply' (adjunction Y X) (adjunction Y' X') f
  exact h

/-- For the chosen right duals, the right mate is Mathlib's `rightAdjointMate`. -/
theorem rightMate_eq_rightAdjointMate [HasRightDual X] [HasRightDual X'] (f : X ⟶ X') :
    rightMate (Xᘁ) (X'ᘁ) f = rightAdjointMate f := by
  rw [rightMate_eq, rightAdjointMate]

/-- For the chosen left duals, the left mate is Mathlib's `leftAdjointMate`. -/
theorem leftMate_eq_leftAdjointMate [HasLeftDual X] [HasLeftDual X'] (f : X ⟶ X') :
    leftMate (ᘁX) (ᘁX') f = leftAdjointMate f := by
  rw [leftMate_eq, leftAdjointMate]
  monoidal

theorem rightMate_biadjunction [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y']
    [ExactPairing Y' X'] (f : X ⟶ X') :
    Biadjunction.rightMate (biadjunction X Y) (biadjunction X' Y') f = rightMate Y Y' f := rfl

theorem leftMate_biadjunction [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y']
    [ExactPairing Y' X'] (f : X ⟶ X') :
    Biadjunction.leftMate (biadjunction X Y) (biadjunction X' Y') f = leftMate Y Y' f := rfl

@[simp]
theorem rightMate_id [ExactPairing X Y] : rightMate Y Y (𝟙 X) = 𝟙 Y :=
  Bicategory.conjugateEquiv_id _

@[simp]
theorem leftMate_id [ExactPairing Y X] : leftMate Y Y (𝟙 X) = 𝟙 Y :=
  Bicategory.conjugateEquiv_symm_id _

theorem rightMate_comp [ExactPairing X Y] [ExactPairing X' Y'] [ExactPairing X'' Y'']
    (f : X ⟶ X') (g : X' ⟶ X'') :
    rightMate Y Y'' (f ≫ g) = rightMate Y' Y'' g ≫ rightMate Y Y' f :=
  (Bicategory.conjugateEquiv_comp _ _ _ _ _).symm

theorem leftMate_comp [ExactPairing Y X] [ExactPairing Y' X'] [ExactPairing Y'' X'']
    (f : X ⟶ X') (g : X' ⟶ X'') :
    leftMate Y Y'' (f ≫ g) = leftMate Y' Y'' g ≫ leftMate Y Y' f :=
  (Bicategory.conjugateEquiv_symm_comp _ _ _ _ _).symm

/-- A morphism `f : X ⟶ X'` between objects with bidualities is cyclic if its right and left
mates agree. -/
def IsCyclic [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y'] [ExactPairing Y' X']
    (f : X ⟶ X') : Prop :=
  rightMate Y Y' f = leftMate Y Y' f

theorem isCyclic_iff [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y']
    [ExactPairing Y' X'] (f : X ⟶ X') :
    IsCyclic Y Y' f ↔ (biadjunction X Y).IsCyclic (biadjunction X' Y') f := Iff.rfl

theorem isCyclic_id [ExactPairing X Y] [ExactPairing Y X] : IsCyclic Y Y (𝟙 X) :=
  (isCyclic_iff Y Y (𝟙 X)).2 (Biadjunction.isCyclic_id (biadjunction X Y))

variable {Y Y' Y''} in
theorem IsCyclic.comp [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y']
    [ExactPairing Y' X'] [ExactPairing X'' Y''] [ExactPairing Y'' X''] {f : X ⟶ X'}
    {g : X' ⟶ X''} (hf : IsCyclic Y Y' f) (hg : IsCyclic Y' Y'' g) :
    IsCyclic Y Y'' (f ≫ g) :=
  (isCyclic_iff Y Y'' (f ≫ g)).2
    (Biadjunction.IsCyclic.comp ((isCyclic_iff Y Y' f).1 hf) ((isCyclic_iff Y' Y'' g).1 hg))

/-- The mates of a morphism with respect to the exchanged bidualities, in the opposite
rotational direction, recover the morphism. -/
theorem rightMate_leftMate [ExactPairing Y X] [ExactPairing Y' X'] (f : X ⟶ X') :
    rightMate X' X (leftMate Y Y' f) = f :=
  Equiv.apply_symm_apply _ f

theorem leftMate_rightMate [ExactPairing X Y] [ExactPairing X' Y'] (f : X ⟶ X') :
    leftMate X' X (rightMate Y Y' f) = f :=
  Equiv.symm_apply_apply _ f

variable {Y Y'} in
/-- The right mate of a cyclic morphism is cyclic, for the exchanged bidualities. -/
theorem IsCyclic.rightMate [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y']
    [ExactPairing Y' X'] {f : X ⟶ X'} (hf : IsCyclic Y Y' f) :
    IsCyclic X' X (MonoidalDuality.rightMate Y Y' f) :=
  Biadjunction.IsCyclic.rightMate (P := biadjunction X Y) (P' := biadjunction X' Y') hf

end Mates

/-! ## Traces -/

section Traces

variable {X X' : C} (Y Y' : C)

/-- The right trace `η_ X Y ≫ f ▷ Y ≫ ε_ Y X` of `f : X ⟶ X`. -/
def rightTrace [ExactPairing X Y] [ExactPairing Y X] (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Y ≫ f ▷ Y ≫ ε_ Y X

/-- The left trace `η_ Y X ≫ Y ◁ f ≫ ε_ X Y` of `f : X ⟶ X`. -/
def leftTrace [ExactPairing X Y] [ExactPairing Y X] (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ Y X ≫ Y ◁ f ≫ ε_ X Y

theorem rightTrace_biadjunction [ExactPairing X Y] [ExactPairing Y X] (f : X ⟶ X) :
    (biadjunction X Y).rightTrace f = rightTrace Y f := rfl

theorem leftTrace_biadjunction [ExactPairing X Y] [ExactPairing Y X] (f : X ⟶ X) :
    (biadjunction X Y).leftTrace f = leftTrace Y f := rfl

theorem rightTrace_id [ExactPairing X Y] [ExactPairing Y X] :
    rightTrace Y (𝟙 X) = η_ X Y ≫ ε_ Y X := by
  simp [rightTrace]

theorem leftTrace_id [ExactPairing X Y] [ExactPairing Y X] :
    leftTrace Y (𝟙 X) = η_ Y X ≫ ε_ X Y := by
  simp [leftTrace]

variable {Y Y'}

variable [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y'] [ExactPairing Y' X']

theorem rightTrace_comp_comm_of_isCyclic_left {f : X ⟶ X'} (hf : IsCyclic Y Y' f)
    (g : X' ⟶ X) : rightTrace Y (f ≫ g) = rightTrace Y' (g ≫ f) :=
  Biadjunction.rightTrace_comp_comm_of_isCyclic_left (P := biadjunction X Y)
    (P' := biadjunction X' Y') hf g

theorem rightTrace_comp_comm_of_isCyclic_right (f : X ⟶ X') {g : X' ⟶ X}
    (hg : IsCyclic Y' Y g) : rightTrace Y (f ≫ g) = rightTrace Y' (g ≫ f) :=
  Biadjunction.rightTrace_comp_comm_of_isCyclic_right (P := biadjunction X Y)
    (P' := biadjunction X' Y') f hg

theorem leftTrace_comp_comm_of_isCyclic_left {f : X ⟶ X'} (hf : IsCyclic Y Y' f)
    (g : X' ⟶ X) : leftTrace Y (f ≫ g) = leftTrace Y' (g ≫ f) :=
  Biadjunction.leftTrace_comp_comm_of_isCyclic_left (P := biadjunction X Y)
    (P' := biadjunction X' Y') hf g

theorem leftTrace_comp_comm_of_isCyclic_right (f : X ⟶ X') {g : X' ⟶ X}
    (hg : IsCyclic Y' Y g) : leftTrace Y (f ≫ g) = leftTrace Y' (g ≫ f) :=
  Biadjunction.leftTrace_comp_comm_of_isCyclic_right (P := biadjunction X Y)
    (P' := biadjunction X' Y') f hg

/-- The right trace of `f` is the left trace of its right mate. -/
theorem rightTrace_eq_leftTrace_rightMate (f : X ⟶ X) :
    rightTrace Y f = leftTrace X (rightMate Y Y f) :=
  Biadjunction.rightTrace_eq_leftTrace_rightMate (biadjunction X Y) f

/-- The right trace of `f` is the left trace of its left mate. -/
theorem rightTrace_eq_leftTrace_leftMate (f : X ⟶ X) :
    rightTrace Y f = leftTrace X (leftMate Y Y f) :=
  Biadjunction.rightTrace_eq_leftTrace_leftMate (biadjunction X Y) f

/-- The left trace of `f` is the right trace of its right mate. -/
theorem leftTrace_eq_rightTrace_rightMate (f : X ⟶ X) :
    leftTrace Y f = rightTrace X (rightMate Y Y f) :=
  Biadjunction.leftTrace_eq_rightTrace_rightMate (biadjunction X Y) f

/-- The left trace of `f` is the right trace of its left mate. -/
theorem leftTrace_eq_rightTrace_leftMate (f : X ⟶ X) :
    leftTrace Y f = rightTrace X (leftMate Y Y f) :=
  Biadjunction.leftTrace_eq_rightTrace_leftMate (biadjunction X Y) f

end Traces

/-! ## Linear structure -/

section Linear

instance instPreadditiveHom [Preadditive C] (a b : MonoidalSingleObj.{u, v, w + 1} C) :
    Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive C)

instance instLinearHom (R : Type*) [Semiring R] [Preadditive C] [Linear R C]
    (a b : MonoidalSingleObj.{u, v, w + 1} C) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R C)

instance [Preadditive C] [MonoidalPreadditive C] :
    LocallyPreadditive (MonoidalSingleObj.{u, v, w + 1} C) where
  whiskerLeft_add f _ _ η θ := MonoidalPreadditive.whiskerLeft_add (C := C) (X := f) η θ
  add_whiskerRight η θ h := MonoidalPreadditive.add_whiskerRight (C := C) (X := h) η θ

instance (R : Type*) [Semiring R] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
    [MonoidalLinear R C] :
    LocallyLinear R (MonoidalSingleObj.{u, v, w + 1} C) where
  whiskerLeft_smul f _ _ r η := MonoidalLinear.whiskerLeft_smul (C := C) f r η
  smul_whiskerRight r η h := MonoidalLinear.smul_whiskerRight (C := C) r η h

variable [Preadditive C] [MonoidalPreadditive C] {X X' : C} {Y Y' : C}

theorem rightMate_add [ExactPairing X Y] [ExactPairing X' Y'] (f g : X ⟶ X') :
    rightMate Y Y' (f + g) = rightMate Y Y' f + rightMate Y Y' g := by
  simp only [rightMate_eq, MonoidalPreadditive.whiskerLeft_add,
    MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

theorem leftMate_add [ExactPairing Y X] [ExactPairing Y' X'] (f g : X ⟶ X') :
    leftMate Y Y' (f + g) = leftMate Y Y' f + leftMate Y Y' g := by
  simp only [leftMate_eq, MonoidalPreadditive.whiskerLeft_add,
    MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

variable [ExactPairing X Y] [ExactPairing Y X]

theorem IsCyclic.add [ExactPairing X' Y'] [ExactPairing Y' X'] {f g : X ⟶ X'}
    (hf : IsCyclic Y Y' f) (hg : IsCyclic Y Y' g) : IsCyclic Y Y' (f + g) := by
  rw [IsCyclic, rightMate_add, leftMate_add, hf, hg]

theorem rightTrace_add (f g : X ⟶ X) : rightTrace Y (f + g) = rightTrace Y f + rightTrace Y g :=
  Biadjunction.rightTrace_add (biadjunction X Y) f g

theorem leftTrace_add (f g : X ⟶ X) : leftTrace Y (f + g) = leftTrace Y f + leftTrace Y g :=
  Biadjunction.leftTrace_add (biadjunction X Y) f g

variable {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C]

theorem rightTrace_smul (r : R) (f : X ⟶ X) : rightTrace Y (r • f) = r • rightTrace Y f :=
  Biadjunction.rightTrace_smul (biadjunction X Y) r f

theorem leftTrace_smul (r : R) (f : X ⟶ X) : leftTrace Y (r • f) = r • leftTrace Y f :=
  Biadjunction.leftTrace_smul (biadjunction X Y) r f

theorem IsCyclic.smul [ExactPairing X' Y'] [ExactPairing Y' X'] {f : X ⟶ X'}
    (hf : IsCyclic Y Y' f) (r : R) : IsCyclic Y Y' (r • f) :=
  Biadjunction.IsCyclic.smul (P := biadjunction X Y) (P' := biadjunction X' Y') hf r

end Linear

end MonoidalDuality

end StringDiagrams
