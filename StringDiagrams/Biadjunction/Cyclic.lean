import StringDiagrams.Biadjunction.Basic
import StringDiagrams.Biadjunction.Conjugate
import Mathlib.CategoryTheory.EqToHom

/-!
# Mates and cyclic 2-morphisms

Properties of the right and left mates of a 2-morphism between 1-morphisms with chosen
biadjunctions, and closure properties of cyclic 2-morphisms (`Biadjunction.IsCyclic`).

## Main results

* Functoriality: `rightMate_id`, `leftMate_id`, and `rightMate_comp`, `leftMate_comp`
  (mates reverse the order of vertical composition); `doubleMate_id`, `doubleMate_comp`.
* Whiskering (for composite biadjunctions `Biadjunction.comp`): `rightMate_whiskerRight`,
  `leftMate_whiskerRight`, `rightMate_whiskerLeft`, `leftMate_whiskerLeft`.
* Mates of mates (`Biadjunction.symm`): `rightMate_symm_leftMate`, `leftMate_symm_rightMate`
  (the mates of `α` with respect to the exchanged biadjunctions, taken in the opposite
  rotational direction, return `α`) and `rightMate_symm`, `leftMate_symm`.
* Cyclic 2-morphisms: `isCyclic_id`, `IsCyclic.comp`, `IsCyclic.whiskerRight`,
  `IsCyclic.whiskerLeft`, `IsCyclic.hcomp`, `IsCyclic.inv`, `IsCyclic.rightMate`,
  `IsCyclic.leftMate`; the associators and unitors are cyclic for the composite
  biadjunctions (`isCyclic_associator_hom`, `isCyclic_leftUnitor_hom`, ...), and
  `isCyclic_eqToHom` for biadjunctions identified along equalities of 1-morphisms.
* Units and counits: the unit of `f ⊣ g` is cyclic with respect to `Biadjunction.id` and
  `P.comp P.symm`, and both of its mates are the counit of `g ⊣ f`
  (`rightMate_left_unit`, `leftMate_left_unit`, `isCyclic_left_unit`); similarly for the
  unit of `g ⊣ f` and for the two counits.
* `rightMate_eq_comp`, `leftMate_eq_comp`: changing the biadjunctions conjugates the mates
  by the mates of identities.
-/

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

namespace Biadjunction

variable {a b c d : B}

section Vertical

variable {f f' f'' : a ⟶ b} {g g' g'' : b ⟶ a}

@[simp]
theorem rightMate_id (P : f ⊣⊢ g) : rightMate P P (𝟙 f) = 𝟙 g :=
  conjugateEquiv_id _

@[simp]
theorem leftMate_id (P : f ⊣⊢ g) : leftMate P P (𝟙 f) = 𝟙 g :=
  conjugateEquiv_symm_id _

theorem rightMate_comp (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (P'' : f'' ⊣⊢ g'') (α : f ⟶ f')
    (β : f' ⟶ f'') :
    rightMate P P'' (α ≫ β) = rightMate P' P'' β ≫ rightMate P P' α :=
  (conjugateEquiv_comp _ _ _ _ _).symm

theorem leftMate_comp (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (P'' : f'' ⊣⊢ g'') (α : f ⟶ f')
    (β : f' ⟶ f'') :
    leftMate P P'' (α ≫ β) = leftMate P' P'' β ≫ leftMate P P' α :=
  (conjugateEquiv_symm_comp _ _ _ _ _).symm

@[simp]
theorem doubleMate_id (P : f ⊣⊢ g) : doubleMate P P (𝟙 f) = 𝟙 f := by
  rw [doubleMate, rightMate_id, Equiv.symm_apply_eq, leftMate_id]

theorem doubleMate_comp (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (P'' : f'' ⊣⊢ g'') (α : f ⟶ f')
    (β : f' ⟶ f'') :
    doubleMate P P'' (α ≫ β) = doubleMate P P' α ≫ doubleMate P' P'' β := by
  rw [doubleMate, Equiv.symm_apply_eq, leftMate_comp P P' P'', doubleMate, doubleMate,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, rightMate_comp]

/-- Changing the biadjunctions on the source and target conjugates the right mate by the right
mates of identities. -/
theorem rightMate_eq_comp (P Q : f ⊣⊢ g) (P' Q' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMate P P' α = rightMate Q' P' (𝟙 f') ≫ rightMate Q Q' α ≫ rightMate P Q (𝟙 f) := by
  rw [← rightMate_comp, ← rightMate_comp, Category.id_comp, Category.comp_id]

/-- Changing the biadjunctions on the source and target conjugates the left mate by the left
mates of identities. -/
theorem leftMate_eq_comp (P Q : f ⊣⊢ g) (P' Q' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMate P P' α = leftMate Q' P' (𝟙 f') ≫ leftMate Q Q' α ≫ leftMate P Q (𝟙 f) := by
  rw [← leftMate_comp, ← leftMate_comp, Category.id_comp, Category.comp_id]

end Vertical

section Change

variable {f f' : a ⟶ b} {g g' h h' : b ⟶ a}

/-- `rightMate_eq_comp` for biadjunctions with different chosen biadjoints. -/
theorem rightMate_eq_comp' (P : f ⊣⊢ g) (Q : f ⊣⊢ h) (P' : f' ⊣⊢ g') (Q' : f' ⊣⊢ h')
    (α : f ⟶ f') :
    rightMate P P' α = rightMate Q' P' (𝟙 f') ≫ rightMate Q Q' α ≫ rightMate P Q (𝟙 f) := by
  simp only [rightMate]
  rw [conjugateEquiv_comp, conjugateEquiv_comp, Category.id_comp, Category.comp_id]

/-- `leftMate_eq_comp` for biadjunctions with different chosen biadjoints. -/
theorem leftMate_eq_comp' (P : f ⊣⊢ g) (Q : f ⊣⊢ h) (P' : f' ⊣⊢ g') (Q' : f' ⊣⊢ h')
    (α : f ⟶ f') :
    leftMate P P' α = leftMate Q' P' (𝟙 f') ≫ leftMate Q Q' α ≫ leftMate P Q (𝟙 f) := by
  simp only [leftMate]
  rw [conjugateEquiv_symm_comp, conjugateEquiv_symm_comp, Category.id_comp, Category.comp_id]

end Change

section Symm

variable {f f' : a ⟶ b} {g g' : b ⟶ a}

/-- The right mate with respect to the exchanged biadjunctions is the inverse of the left
mate. -/
theorem rightMate_symm (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') :
    rightMate P'.symm P.symm = (leftMate P P').symm := rfl

/-- The left mate with respect to the exchanged biadjunctions is the inverse of the right
mate. -/
theorem leftMate_symm (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') :
    leftMate P'.symm P.symm = (rightMate P P').symm := rfl

@[simp]
theorem rightMate_symm_leftMate (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMate P'.symm P.symm (leftMate P P' α) = α :=
  Equiv.apply_symm_apply (conjugateEquiv P.right P'.right) α

@[simp]
theorem leftMate_symm_rightMate (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMate P'.symm P.symm (rightMate P P' α) = α :=
  Equiv.symm_apply_apply _ _

@[simp]
theorem leftMate_symm_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (β : g' ⟶ g) :
    leftMate P P' ((leftMate P P').symm β) = β :=
  Equiv.apply_symm_apply _ _

/-- The double mate is the right mate taken twice, the second time with respect to the
exchanged biadjunctions. -/
theorem doubleMate_eq (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    doubleMate P P' α = rightMate P'.symm P.symm (rightMate P P' α) := rfl

end Symm

/-! ## Cyclic 2-morphisms -/

section Cyclic

variable {f f' f'' : a ⟶ b} {g g' g'' : b ⟶ a}

theorem isCyclic_id (P : f ⊣⊢ g) : IsCyclic P P (𝟙 f) := by
  rw [IsCyclic, rightMate_id, leftMate_id]

theorem IsCyclic.eq {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'} (h : IsCyclic P P' α) :
    rightMate P P' α = leftMate P P' α := h

theorem IsCyclic.doubleMate_eq {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (h : IsCyclic P P' α) : doubleMate P P' α = α :=
  (isCyclic_iff_doubleMate_eq P P' α).1 h

theorem IsCyclic.comp {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {P'' : f'' ⊣⊢ g''} {α : f ⟶ f'}
    {β : f' ⟶ f''} (hα : IsCyclic P P' α) (hβ : IsCyclic P' P'' β) :
    IsCyclic P P'' (α ≫ β) := by
  rw [IsCyclic, rightMate_comp P P' P'', leftMate_comp P P' P'', hα.eq, hβ.eq]

theorem IsCyclic.inv {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'} [IsIso α]
    (h : IsCyclic P P' α) : IsCyclic P' P (CategoryTheory.inv α) := by
  have hr : rightMate P' P (CategoryTheory.inv α) ≫ rightMate P P' α = 𝟙 _ := by
    rw [← rightMate_comp, IsIso.hom_inv_id, rightMate_id]
  have hl : leftMate P' P (CategoryTheory.inv α) ≫ leftMate P P' α = 𝟙 _ := by
    rw [← leftMate_comp, IsIso.hom_inv_id, leftMate_id]
  have : IsIso (rightMate P P' α) :=
    ⟨rightMate P' P (CategoryTheory.inv α),
      by rw [← rightMate_comp, IsIso.inv_hom_id, rightMate_id], hr⟩
  rw [← h.eq] at hl
  rw [IsCyclic, IsIso.eq_inv_of_inv_hom_id hr, IsIso.eq_inv_of_inv_hom_id hl]

theorem IsCyclic.iso_inv {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {e : f ≅ f'}
    (h : IsCyclic P P' e.hom) : IsCyclic P' P e.inv := by
  have := h.inv
  rwa [IsIso.Iso.inv_hom] at this

/-- The right mate of a cyclic 2-morphism is cyclic, for the exchanged biadjunctions. -/
theorem IsCyclic.rightMate {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (h : IsCyclic P P' α) : IsCyclic P'.symm P.symm (rightMate P P' α) := by
  rw [IsCyclic, leftMate_symm_rightMate]
  conv_lhs => rw [h.eq]
  exact rightMate_symm_leftMate P P' α

/-- The left mate of a cyclic 2-morphism is cyclic, for the exchanged biadjunctions. -/
theorem IsCyclic.leftMate {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (h : IsCyclic P P' α) : IsCyclic P'.symm P.symm (leftMate P P' α) := by
  rw [← h.eq]; exact h.rightMate

theorem isCyclic_rightMate_iff (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    IsCyclic P'.symm P.symm (rightMate P P' α) ↔ IsCyclic P P' α := by
  refine ⟨fun h => ?_, IsCyclic.rightMate⟩
  have := h.leftMate
  rwa [leftMate_symm_rightMate] at this

/-- Cyclicity of `β : g' ⟶ g` for the exchanged biadjunctions: the inverses of the two mates
agree. -/
theorem isCyclic_symm_iff (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (β : g' ⟶ g) :
    IsCyclic P'.symm P.symm β ↔ (rightMate P P').symm β = (leftMate P P').symm β := by
  rw [IsCyclic, rightMate_symm, leftMate_symm, eq_comm]

end Cyclic

/-! ## Whiskering -/

section Whisker

variable {f f' : a ⟶ b} {g g' : b ⟶ a}

theorem rightMate_whiskerRight (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') {h : b ⟶ c} {k : c ⟶ b}
    (R : h ⊣⊢ k) (α : f ⟶ f') :
    rightMate (P.comp R) (P'.comp R) (α ▷ h) = k ◁ rightMate P P' α :=
  conjugateEquiv_whiskerRight _ _ _ _

theorem leftMate_whiskerRight (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') {h : b ⟶ c} {k : c ⟶ b}
    (R : h ⊣⊢ k) (α : f ⟶ f') :
    leftMate (P.comp R) (P'.comp R) (α ▷ h) = k ◁ leftMate P P' α :=
  conjugateEquiv_symm_whiskerRight _ _ _ _

theorem rightMate_whiskerLeft (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') {h : c ⟶ a} {k : a ⟶ c}
    (R : h ⊣⊢ k) (α : f ⟶ f') :
    rightMate (R.comp P) (R.comp P') (h ◁ α) = rightMate P P' α ▷ k :=
  conjugateEquiv_whiskerLeft _ _ _ _

theorem leftMate_whiskerLeft (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') {h : c ⟶ a} {k : a ⟶ c}
    (R : h ⊣⊢ k) (α : f ⟶ f') :
    leftMate (R.comp P) (R.comp P') (h ◁ α) = leftMate P P' α ▷ k :=
  conjugateEquiv_symm_whiskerLeft _ _ _ _

theorem IsCyclic.whiskerRight {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (hα : IsCyclic P P' α) {h : b ⟶ c} {k : c ⟶ b} (R : h ⊣⊢ k) :
    IsCyclic (P.comp R) (P'.comp R) (α ▷ h) := by
  rw [IsCyclic, rightMate_whiskerRight, leftMate_whiskerRight, hα.eq]

theorem IsCyclic.whiskerLeft {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (hα : IsCyclic P P' α) {h : c ⟶ a} {k : a ⟶ c} (R : h ⊣⊢ k) :
    IsCyclic (R.comp P) (R.comp P') (h ◁ α) := by
  rw [IsCyclic, rightMate_whiskerLeft, leftMate_whiskerLeft, hα.eq]

/-- Horizontal composites of cyclic 2-morphisms are cyclic for the composite biadjunctions. -/
theorem IsCyclic.hcomp {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'} {h h' : b ⟶ c}
    {k k' : c ⟶ b} {R : h ⊣⊢ k} {R' : h' ⊣⊢ k'} {β : h ⟶ h'} (hα : IsCyclic P P' α)
    (hβ : IsCyclic R R' β) :
    IsCyclic (P.comp R) (P'.comp R') (α ▷ h ≫ f' ◁ β) :=
  (hα.whiskerRight R).comp (hβ.whiskerLeft P')

end Whisker

/-! ## Units and counits -/

section UnitCounit

variable {f : a ⟶ b} {g : b ⟶ a}

/-- The right mate of the unit of `f ⊣ g` (a 2-morphism `𝟙 a ⟶ f ≫ g`, with the biadjunctions
`Biadjunction.id a` and `P.comp P.symm : f ≫ g ⊣⊢ f ≫ g`) is the counit of `g ⊣ f`. -/
theorem rightMate_left_unit (P : f ⊣⊢ g) :
    rightMate (id a) (P.comp P.symm) P.left.unit = P.right.counit := by
  apply conjugateEquiv_eq_of_unit
  simp only [id_left, comp_left, symm_left, Adjunction.id, Adjunction.comp_unit,
    Adjunction.compUnit]
  symm
  calc
    _ = P.left.unit ⊗≫ f ◁ leftZigzag P.right.unit P.right.counit ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [P.right.left_triangle]; bicategory

/-- The left mate of the unit of `f ⊣ g` is the counit of `g ⊣ f`. -/
theorem leftMate_left_unit (P : f ⊣⊢ g) :
    leftMate (id a) (P.comp P.symm) P.left.unit = P.right.counit := by
  rw [leftMate, Equiv.symm_apply_eq]
  symm
  apply conjugateEquiv_eq_of_unit
  simp only [id_right, comp_right, symm_right, Adjunction.id, Adjunction.comp_unit,
    Adjunction.compUnit]
  calc
    _ = P.left.unit ⊗≫ rightZigzag P.right.unit P.right.counit ▷ g ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [P.right.right_triangle]; bicategory

/-- The unit of `f ⊣ g` is cyclic for the biadjunctions `Biadjunction.id a` and
`P.comp P.symm`. -/
theorem isCyclic_left_unit (P : f ⊣⊢ g) : IsCyclic (id a) (P.comp P.symm) P.left.unit := by
  rw [IsCyclic, rightMate_left_unit, leftMate_left_unit]

/-- The right mate of the unit of `g ⊣ f` is the counit of `f ⊣ g`. -/
theorem rightMate_right_unit (P : f ⊣⊢ g) :
    rightMate (id b) (P.symm.comp P) P.right.unit = P.left.counit :=
  rightMate_left_unit P.symm

/-- The left mate of the unit of `g ⊣ f` is the counit of `f ⊣ g`. -/
theorem leftMate_right_unit (P : f ⊣⊢ g) :
    leftMate (id b) (P.symm.comp P) P.right.unit = P.left.counit :=
  leftMate_left_unit P.symm

/-- The unit of `g ⊣ f` is cyclic for the biadjunctions `Biadjunction.id b` and
`P.symm.comp P`. -/
theorem isCyclic_right_unit (P : f ⊣⊢ g) : IsCyclic (id b) (P.symm.comp P) P.right.unit :=
  isCyclic_left_unit P.symm

/-- The right mate of the counit of `f ⊣ g` (a 2-morphism `g ≫ f ⟶ 𝟙 b`, with the
biadjunctions `P.symm.comp P : g ≫ f ⊣⊢ g ≫ f` and `Biadjunction.id b`) is the unit of
`g ⊣ f`. -/
theorem rightMate_left_counit (P : f ⊣⊢ g) :
    rightMate (P.symm.comp P) (id b) P.left.counit = P.right.unit := by
  rw [← leftMate_right_unit P]
  exact rightMate_symm_leftMate (id b) (P.symm.comp P) P.right.unit

/-- The left mate of the counit of `f ⊣ g` is the unit of `g ⊣ f`. -/
theorem leftMate_left_counit (P : f ⊣⊢ g) :
    leftMate (P.symm.comp P) (id b) P.left.counit = P.right.unit := by
  rw [← rightMate_right_unit P]
  exact leftMate_symm_rightMate (id b) (P.symm.comp P) P.right.unit

/-- The counit of `f ⊣ g` is cyclic for the biadjunctions `P.symm.comp P` and
`Biadjunction.id b`. -/
theorem isCyclic_left_counit (P : f ⊣⊢ g) : IsCyclic (P.symm.comp P) (id b) P.left.counit := by
  rw [IsCyclic, rightMate_left_counit, leftMate_left_counit]

/-- The right mate of the counit of `g ⊣ f` is the unit of `f ⊣ g`. -/
theorem rightMate_right_counit (P : f ⊣⊢ g) :
    rightMate (P.comp P.symm) (id a) P.right.counit = P.left.unit :=
  rightMate_left_counit P.symm

/-- The left mate of the counit of `g ⊣ f` is the unit of `f ⊣ g`. -/
theorem leftMate_right_counit (P : f ⊣⊢ g) :
    leftMate (P.comp P.symm) (id a) P.right.counit = P.left.unit :=
  leftMate_left_counit P.symm

/-- The counit of `g ⊣ f` is cyclic for the biadjunctions `P.comp P.symm` and
`Biadjunction.id a`. -/
theorem isCyclic_right_counit (P : f ⊣⊢ g) :
    IsCyclic (P.comp P.symm) (id a) P.right.counit :=
  isCyclic_left_counit P.symm

end UnitCounit

/-! ## Coherence 2-morphisms -/

section Coherence

variable {e : B} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b} {f₃ : c ⟶ e} {g₃ : e ⟶ c}

theorem rightMate_associator_hom (P : f₁ ⊣⊢ g₁) (Q : f₂ ⊣⊢ g₂) (R : f₃ ⊣⊢ g₃) :
    rightMate ((P.comp Q).comp R) (P.comp (Q.comp R)) (α_ f₁ f₂ f₃).hom =
      (α_ g₃ g₂ g₁).hom := by
  apply conjugateEquiv_eq_of_unit
  simp only [comp_left, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

theorem leftMate_associator_hom (P : f₁ ⊣⊢ g₁) (Q : f₂ ⊣⊢ g₂) (R : f₃ ⊣⊢ g₃) :
    leftMate ((P.comp Q).comp R) (P.comp (Q.comp R)) (α_ f₁ f₂ f₃).hom =
      (α_ g₃ g₂ g₁).hom := by
  rw [leftMate, Equiv.symm_apply_eq]
  symm
  apply conjugateEquiv_eq_of_unit
  simp only [comp_right, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

/-- The associator is cyclic for the composite biadjunctions. -/
theorem isCyclic_associator_hom (P : f₁ ⊣⊢ g₁) (Q : f₂ ⊣⊢ g₂) (R : f₃ ⊣⊢ g₃) :
    IsCyclic ((P.comp Q).comp R) (P.comp (Q.comp R)) (α_ f₁ f₂ f₃).hom := by
  rw [IsCyclic, rightMate_associator_hom, leftMate_associator_hom]

theorem isCyclic_associator_inv (P : f₁ ⊣⊢ g₁) (Q : f₂ ⊣⊢ g₂) (R : f₃ ⊣⊢ g₃) :
    IsCyclic (P.comp (Q.comp R)) ((P.comp Q).comp R) (α_ f₁ f₂ f₃).inv :=
  (isCyclic_associator_hom P Q R).iso_inv

theorem rightMate_leftUnitor_hom (P : f₁ ⊣⊢ g₁) :
    rightMate ((id a).comp P) P (λ_ f₁).hom = (ρ_ g₁).inv := by
  apply conjugateEquiv_eq_of_unit
  simp only [comp_left, id_left, Adjunction.id, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

theorem leftMate_leftUnitor_hom (P : f₁ ⊣⊢ g₁) :
    leftMate ((id a).comp P) P (λ_ f₁).hom = (ρ_ g₁).inv := by
  rw [leftMate, Equiv.symm_apply_eq]
  symm
  apply conjugateEquiv_eq_of_unit
  simp only [comp_right, id_right, Adjunction.id, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

/-- The left unitor is cyclic for the biadjunctions `(id a).comp P` and `P`. -/
theorem isCyclic_leftUnitor_hom (P : f₁ ⊣⊢ g₁) : IsCyclic ((id a).comp P) P (λ_ f₁).hom := by
  rw [IsCyclic, rightMate_leftUnitor_hom, leftMate_leftUnitor_hom]

theorem isCyclic_leftUnitor_inv (P : f₁ ⊣⊢ g₁) : IsCyclic P ((id a).comp P) (λ_ f₁).inv :=
  (isCyclic_leftUnitor_hom P).iso_inv

theorem rightMate_rightUnitor_hom (P : f₁ ⊣⊢ g₁) :
    rightMate (P.comp (id b)) P (ρ_ f₁).hom = (λ_ g₁).inv := by
  apply conjugateEquiv_eq_of_unit
  simp only [comp_left, id_left, Adjunction.id, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

theorem leftMate_rightUnitor_hom (P : f₁ ⊣⊢ g₁) :
    leftMate (P.comp (id b)) P (ρ_ f₁).hom = (λ_ g₁).inv := by
  rw [leftMate, Equiv.symm_apply_eq]
  symm
  apply conjugateEquiv_eq_of_unit
  simp only [comp_right, id_right, Adjunction.id, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

/-- The right unitor is cyclic for the biadjunctions `P.comp (id b)` and `P`. -/
theorem isCyclic_rightUnitor_hom (P : f₁ ⊣⊢ g₁) : IsCyclic (P.comp (id b)) P (ρ_ f₁).hom := by
  rw [IsCyclic, rightMate_rightUnitor_hom, leftMate_rightUnitor_hom]

theorem isCyclic_rightUnitor_inv (P : f₁ ⊣⊢ g₁) : IsCyclic P (P.comp (id b)) (ρ_ f₁).inv :=
  (isCyclic_rightUnitor_hom P).iso_inv

/-- `eqToHom` is cyclic for biadjunctions which agree along the equalities of 1-morphisms. -/
theorem isCyclic_eqToHom {f f' : a ⟶ b} {g g' : b ⟶ a} {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'}
    (hf : f = f') (hg : g = g') (hP : HEq P P') : IsCyclic P P' (eqToHom hf) := by
  subst hf hg
  cases eq_of_heq hP
  exact isCyclic_id P

end Coherence

end Biadjunction

end StringDiagrams
