/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.GradedMonoidal
import StringDiagrams.Super.GradedTwo
import StringDiagrams.Super.KarBicategory
import StringDiagrams.Super.K0Ring
import StringDiagrams.Super.GSVecMonoidal

/-!
# A monoidal supercategory as a 2-supercategory with one object

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §1.7: a monoidal
(super)category is a 2-(super)category with one object, and the constructions of §§4–6 for
2-supercategories specialize to monoidal supercategories this way (for instance the
`(Q, Π)`-envelope, Definition 1.16 and Definition 6.10).

For a monoidal supercategory `C` (Definition 1.4, `MonoidalSupercategory`), `MonoidalTwo C` is
the bicategory with one object whose 1-morphisms are the objects of `C`, with horizontal
composition `X ≫ Y := X ⊗ Y`, identity `𝟙_ C`, whiskerings, associator and unitors those of
`C`, and 2-morphism supercategories `C`. It is a 2-supercategory (Definition 2.2,
`MonoidalTwo.instTwoSupercategory`), graded when `C` is a graded monoidal supercategory
(Definition 6.2, `MonoidalTwo.instGradedTwoSupercategory`), so the graded super Karoubi envelope
`GSKAR` and its split Grothendieck ring `K₀Ring` apply to it. Products in `K₀Ring` are horizontal
composites, here tensor products of objects of the envelope.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory GradedSupercategory

universe w w₁ w₂

/-- A monoidal supercategory `C` viewed as a 2-supercategory with one object (Brundan–Ellis,
*Monoidal supercategories*, §1.7). The parameter `C` only fixes the 1-morphisms. -/
@[nolint unusedArguments]
def MonoidalTwo (_C : Type w₁) : Type := Unit

namespace MonoidalTwo

variable (C : Type w₁) [Category.{w₂} C] [MonoidalCategoryStruct C]

/-- The unique object. -/
def star : MonoidalTwo C := ()

instance : Unique (MonoidalTwo C) := inferInstanceAs (Unique Unit)

/-- Horizontal composition is the tensor product, the identity 1-morphism is the unit object. -/
instance instBicategoryStruct : BicategoryStruct.{w₂, w₁} (MonoidalTwo C) where
  Hom _ _ := C
  id _ := 𝟙_ C
  comp X Y := X ⊗ Y
  homCategory _ _ := inferInstanceAs (Category C)
  whiskerLeft X _ _ η := X ◁ η
  whiskerRight η Y := η ▷ Y
  associator X Y Z := α_ X Y Z
  leftUnitor X := λ_ X
  rightUnitor X := ρ_ X

variable {C}

/-- An object of `C` as a 1-morphism of `MonoidalTwo C`. -/
abbrev of (X : C) : star C ⟶ star C := X

@[simp] theorem comp_def {a b c : MonoidalTwo C} (X : a ⟶ b) (Y : b ⟶ c) :
    X ≫ Y = ((X : C) ⊗ (Y : C) : C) := rfl

theorem whiskerLeft_def {a b c : MonoidalTwo C} (X : a ⟶ b) {Y Z : b ⟶ c} (η : Y ⟶ Z) :
    BicategoryStruct.whiskerLeft X η = MonoidalCategoryStruct.whiskerLeft (C := C) X η := rfl

theorem whiskerRight_def {a b c : MonoidalTwo C} {X Y : a ⟶ b} (η : X ⟶ Y) (Z : b ⟶ c) :
    BicategoryStruct.whiskerRight η Z = MonoidalCategoryStruct.whiskerRight (C := C) η Z := rfl

variable (R : Type w) [CommRing R] [Preadditive C] [Linear R C] [Supercategory R C]

instance (a b : MonoidalTwo C) : Preadditive (a ⟶ b) := inferInstanceAs (Preadditive C)

instance (a b : MonoidalTwo C) : Linear R (a ⟶ b) := inferInstanceAs (Linear R C)

instance (a b : MonoidalTwo C) : Supercategory R (a ⟶ b) := inferInstanceAs (Supercategory R C)

section Two

variable [MonoidalSupercategory R C]

include R in
open MonoidalSupercategory in
private theorem tensorHom_id_left {X : C} {Y Z : C} (g : Y ⟶ Z) :
    (𝟙 X ⊗ₘ g) = X ◁ g := by
  rw [MonoidalSupercategory.tensorHom_def (R := R), id_whiskerRight (R := R), Category.id_comp]

include R in
open MonoidalSupercategory in
private theorem tensorHom_id_right {X Y : C} (f : X ⟶ Y) (Z : C) :
    (f ⊗ₘ 𝟙 Z) = f ▷ Z := by
  rw [MonoidalSupercategory.tensorHom_def (R := R), whiskerLeft_id (R := R), Category.comp_id]

open MonoidalSupercategory in
/-- **Brundan–Ellis, *Monoidal supercategories*, §1.7 and Definition 2.2.** A monoidal
supercategory is a 2-supercategory with one object. -/
instance instTwoSupercategory : TwoSupercategory R (MonoidalTwo C) where
  whiskerLeft_id X Y := whiskerLeft_id (R := R) (C := C) X Y
  whiskerLeft_comp X _ _ _ η θ := whiskerLeft_comp (R := R) (C := C) X η θ
  id_whiskerLeft {_ _ X Y} η := by
    change 𝟙_ C ◁ η = (λ_ X).hom ≫ η ≫ (λ_ Y).inv
    rw [← Category.assoc, ← leftUnitor_naturality (R := R), Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
    rfl
  comp_whiskerLeft {_ _ _ _} X Y {Z Z'} η := by
    change (X ⊗ Y) ◁ η = (α_ X Y Z).hom ≫ X ◁ Y ◁ η ≫ (α_ X Y Z').inv
    have h := associator_naturality (R := R) (𝟙 X) (𝟙 Y) η
    simp only [tensorHom_id_left (R := R), whiskerLeft_id (R := R)] at h
    rw [← Category.assoc, ← h]
    simp
  id_whiskerRight X Y := id_whiskerRight (R := R) (C := C) X Y
  comp_whiskerRight η θ Z := comp_whiskerRight (R := R) (C := C) η θ Z
  whiskerRight_id {_ _ X Y} η := by
    change η ▷ 𝟙_ C = (ρ_ X).hom ≫ η ≫ (ρ_ Y).inv
    rw [← Category.assoc, ← rightUnitor_naturality (R := R), Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
    rfl
  whiskerRight_comp {_ _ _ _ X X'} η Y Z := by
    change η ▷ (Y ⊗ Z) = (α_ X Y Z).inv ≫ η ▷ Y ▷ Z ≫ (α_ X' Y Z).hom
    have h := associator_naturality (R := R) η (𝟙 Y) (𝟙 Z)
    simp only [tensorHom_id_left (R := R), whiskerLeft_id (R := R),
      tensorHom_id_right (R := R)] at h
    rw [h]
    simp
  whisker_assoc {_ _ _ _} X {Y Y'} η Z := by
    change (X ◁ η) ▷ Z = (α_ X Y Z).hom ≫ X ◁ (η ▷ Z) ≫ (α_ X Y' Z).inv
    have h := associator_naturality (R := R) (𝟙 X) η (𝟙 Z)
    simp only [tensorHom_id_left (R := R), tensorHom_id_right (R := R)] at h
    rw [← Category.assoc, ← h]
    simp
  pentagon W X Y Z := pentagon (R := R) (C := C) W X Y Z
  triangle X Y := triangle (R := R) (C := C) X Y
  whiskerLeft_add X _ _ η θ := whiskerLeft_add (R := R) (C := C) X η θ
  add_whiskerRight η θ Z := add_whiskerRight (R := R) (C := C) η θ Z
  whiskerLeft_smul X _ _ r η := whiskerLeft_smul (R := R) (C := C) X r η
  smul_whiskerRight r η Z := smul_whiskerRight (R := R) (C := C) r η Z
  whiskerLeft_mem X _ _ _ _ h := whiskerLeft_mem (R := R) (C := C) X h
  whiskerRight_mem Z h := whiskerRight_mem (R := R) (C := C) Z h
  super_interchange hη hθ := super_interchange (R := R) (C := C) hη hθ
  associator_hom_mem X Y Z := associator_hom_mem (R := R) (C := C) X Y Z
  leftUnitor_hom_mem X := leftUnitor_hom_mem (R := R) (C := C) X
  rightUnitor_hom_mem X := rightUnitor_hom_mem (R := R) (C := C) X

end Two

section Graded

variable [GradedSupercategory R C] [MonoidalSupercategory R C] [GradedMonoidalSupercategory R C]

instance (a b : MonoidalTwo C) : GradedSupercategory R (a ⟶ b) :=
  inferInstanceAs (GradedSupercategory R C)

open GradedMonoidalSupercategory in
/-- **Brundan–Ellis, *Monoidal supercategories*, §1.7 and Definition 6.2.** A graded monoidal
supercategory is a graded 2-supercategory with one object. -/
instance instGradedTwoSupercategory : GradedTwoSupercategory R (MonoidalTwo C) where
  whiskerLeft_mem_degree X _ _ _ _ h := whiskerLeft_mem_degree (R := R) (C := C) X h
  whiskerRight_mem_degree Z h := whiskerRight_mem_degree (R := R) (C := C) Z h
  associator_hom_mem_degree X Y Z := associator_hom_mem_degree (R := R) (C := C) X Y Z
  leftUnitor_hom_mem_degree X := leftUnitor_hom_mem_degree (R := R) (C := C) X
  rightUnitor_hom_mem_degree X := rightUnitor_hom_mem_degree (R := R) (C := C) X

/-- The graded super Karoubi envelope of a graded monoidal supercategory, as a one-object
2-category (`Kar(A̲_{q,π})`, Brundan–Ellis, end of §6, for one object). -/
example : Bicategory (GSKAR R (MonoidalTwo C)) := inferInstance

example (a b : GSKAR R (MonoidalTwo C)) : IsIdempotentComplete (a ⟶ b) := inferInstance

/-- Its split Grothendieck group is a ring under the tensor product (`K₀Ring`). -/
example : NonUnitalRing (K₀Ring (GSKAR R (MonoidalTwo C))) := inferInstance

end Graded

/-- The instances apply to graded superspaces (`GSVec`). -/
example (k : Type w) [Field k] : GradedTwoSupercategory k (MonoidalTwo (GSVec k)) := inferInstance

end MonoidalTwo

end StringDiagrams
