import StringDiagrams.Super.Underlying
import StringDiagrams.Super.Bicategory

/-!
# The underlying bicategory of a 2-supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.1(v) and Definition 2.2(i): the *underlying 2-category* of a 2-supercategory `𝔄`
has the same objects and 1-morphisms, and only the even 2-morphisms. On even 2-morphisms the
super interchange law is the ordinary interchange law, so this is a bicategory in the sense of
Mathlib (`Underlying2.instBicategory`), whose hom categories are the underlying categories
`Underlying R (a ⟶ b)` of the morphism supercategories.

We use it to transport Mathlib's coherence lemmas, which only involve the even coherence maps,
back to the 2-supercategory (`TwoSupercategory.unitors_equal`,
`TwoSupercategory.leftUnitor_comp`, `TwoSupercategory.rightUnitor_comp`, …). We also record the
naturality of the associator and unitors with respect to arbitrary (not necessarily even)
2-morphisms, which follows directly from the axioms.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct

universe w v u w₁

/-- The underlying bicategory of a 2-supercategory (Brundan–Ellis, Definition 1.1(v) applied
to the morphism supercategories): the same objects, 1-morphisms `Underlying R (a ⟶ b)`, and
even 2-morphisms. -/
@[ext]
structure Underlying2 (R : Type w₁) (B : Type u) where
  /-- The object of `B`. -/
  obj : B

namespace Underlying2

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- The bicategory of even 2-morphisms. -/
instance instBicategory : Bicategory (Underlying2 R B) where
  Hom a b := Underlying R (a.obj ⟶ b.obj)
  id a := ⟨𝟙 a.obj⟩
  comp f g := ⟨f.obj ≫ g.obj⟩
  homCategory _ _ := inferInstance
  whiskerLeft f _ _ η := ⟨f.obj ◁ η.1, TwoSupercategory.whiskerLeft_mem f.obj η.2⟩
  whiskerRight η h := ⟨η.1 ▷ h.obj, TwoSupercategory.whiskerRight_mem h.obj η.2⟩
  associator f g h := Underlying.isoMk (associator f.obj g.obj h.obj)
    (TwoSupercategory.associator_hom_mem _ _ _)
  leftUnitor f := Underlying.isoMk (leftUnitor f.obj) (TwoSupercategory.leftUnitor_hom_mem _)
  rightUnitor f := Underlying.isoMk (rightUnitor f.obj) (TwoSupercategory.rightUnitor_hom_mem _)
  whiskerLeft_id f g := Subtype.ext (TwoSupercategory.whiskerLeft_id (R := R) f.obj g.obj)
  whiskerLeft_comp f _ _ _ η θ :=
    Subtype.ext (TwoSupercategory.whiskerLeft_comp (R := R) f.obj η.1 θ.1)
  id_whiskerLeft η := Subtype.ext (TwoSupercategory.id_whiskerLeft (R := R) η.1)
  comp_whiskerLeft f g _ _ η :=
    Subtype.ext (TwoSupercategory.comp_whiskerLeft (R := R) f.obj g.obj η.1)
  id_whiskerRight f g := Subtype.ext (TwoSupercategory.id_whiskerRight (R := R) f.obj g.obj)
  comp_whiskerRight η θ i :=
    Subtype.ext (TwoSupercategory.comp_whiskerRight (R := R) η.1 θ.1 i.obj)
  whiskerRight_id η := Subtype.ext (TwoSupercategory.whiskerRight_id (R := R) η.1)
  whiskerRight_comp η g h :=
    Subtype.ext (TwoSupercategory.whiskerRight_comp (R := R) η.1 g.obj h.obj)
  whisker_assoc f _ _ η h :=
    Subtype.ext (TwoSupercategory.whisker_assoc (R := R) f.obj η.1 h.obj)
  whisker_exchange η θ := Subtype.ext (by
    have := TwoSupercategory.super_interchange (R := R) η.2 θ.2
    rw [koszulSign_zero_left, one_smul] at this
    exact this.symm)
  pentagon f g h i := Subtype.ext (TwoSupercategory.pentagon (R := R) f.obj g.obj h.obj i.obj)
  triangle f g := Subtype.ext (TwoSupercategory.triangle (R := R) f.obj g.obj)

/-- A 1-morphism of `B`, as a 1-morphism of the underlying bicategory. -/
def hom1 {a b : B} (f : a ⟶ b) : (⟨a⟩ : Underlying2 R B) ⟶ ⟨b⟩ := ⟨f⟩

section Simp

variable {a b c d : Underlying2 R B}

@[simp] theorem id_obj (a : Underlying2 R B) : (𝟙 a : a ⟶ a).obj = 𝟙 a.obj := rfl

@[simp] theorem comp_obj (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).obj = f.obj ≫ g.obj := rfl

@[simp] theorem whiskerLeft_val (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (Bicategory.whiskerLeft f η).1 = f.obj ◁ η.1 := rfl

@[simp] theorem whiskerRight_val {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (Bicategory.whiskerRight η h).1 = η.1 ▷ h.obj := rfl

@[simp] theorem associator_hom_val (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (Bicategory.associator f g h).hom.1 = (associator f.obj g.obj h.obj).hom := rfl

@[simp] theorem associator_inv_val (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (Bicategory.associator f g h).inv.1 = (associator f.obj g.obj h.obj).inv := rfl

@[simp] theorem leftUnitor_hom_val (f : a ⟶ b) :
    (Bicategory.leftUnitor f).hom.1 = (leftUnitor f.obj).hom := rfl

@[simp] theorem leftUnitor_inv_val (f : a ⟶ b) :
    (Bicategory.leftUnitor f).inv.1 = (leftUnitor f.obj).inv := rfl

@[simp] theorem rightUnitor_hom_val (f : a ⟶ b) :
    (Bicategory.rightUnitor f).hom.1 = (rightUnitor f.obj).hom := rfl

@[simp] theorem rightUnitor_inv_val (f : a ⟶ b) :
    (Bicategory.rightUnitor f).inv.1 = (rightUnitor f.obj).inv := rfl

end Simp

end Underlying2

/-! ## Coherence lemmas for 2-supercategories -/

namespace TwoSupercategory

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {a b c d e : B}

/-! ### Naturality of the coherence maps (for all 2-morphisms) -/

section Naturality

variable (R)
include R

@[reassoc]
theorem associator_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ g ▷ h ≫ (associator f' g h).hom = (associator f g h).hom ≫ η ▷ (g ≫ h) := by
  rw [whiskerRight_comp (R := R)]; simp

@[reassoc]
theorem associator_inv_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ (g ≫ h) ≫ (associator f' g h).inv = (associator f g h).inv ≫ η ▷ g ▷ h := by
  rw [whiskerRight_comp (R := R)]; simp

@[reassoc]
theorem associator_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    (f ◁ η) ▷ h ≫ (associator f g' h).hom = (associator f g h).hom ≫ f ◁ (η ▷ h) := by
  rw [whisker_assoc (R := R)]; simp

@[reassoc]
theorem associator_inv_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g')
    (h : c ⟶ d) :
    f ◁ (η ▷ h) ≫ (associator f g' h).inv = (associator f g h).inv ≫ (f ◁ η) ▷ h := by
  rw [whisker_assoc (R := R)]; simp

@[reassoc]
theorem associator_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    (f ≫ g) ◁ η ≫ (associator f g h').hom = (associator f g h).hom ≫ f ◁ g ◁ η := by
  rw [comp_whiskerLeft (R := R)]; simp

@[reassoc]
theorem associator_inv_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d}
    (η : h ⟶ h') :
    f ◁ g ◁ η ≫ (associator f g h').inv = (associator f g h).inv ≫ (f ≫ g) ◁ η := by
  rw [comp_whiskerLeft (R := R)]; simp

@[reassoc]
theorem leftUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    𝟙 a ◁ η ≫ (leftUnitor g).hom = (leftUnitor f).hom ≫ η := by
  rw [id_whiskerLeft (R := R)]; simp

@[reassoc]
theorem leftUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ (leftUnitor g).inv = (leftUnitor f).inv ≫ 𝟙 a ◁ η := by
  rw [id_whiskerLeft (R := R)]; simp

@[reassoc]
theorem rightUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝟙 b ≫ (rightUnitor g).hom = (rightUnitor f).hom ≫ η := by
  rw [whiskerRight_id (R := R)]; simp

@[reassoc]
theorem rightUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ (rightUnitor g).inv = (rightUnitor f).inv ≫ η ▷ 𝟙 b := by
  rw [whiskerRight_id (R := R)]; simp

@[simp] theorem whiskerLeft_hom_inv (f : a ⟶ b) {g h : b ⟶ c} (e : g ≅ h) :
    f ◁ e.hom ≫ f ◁ e.inv = 𝟙 (f ≫ g) := by
  rw [← whiskerLeft_comp (R := R), e.hom_inv_id, whiskerLeft_id (R := R)]

@[simp] theorem whiskerLeft_inv_hom (f : a ⟶ b) {g h : b ⟶ c} (e : g ≅ h) :
    f ◁ e.inv ≫ f ◁ e.hom = 𝟙 (f ≫ h) := by
  rw [← whiskerLeft_comp (R := R), e.inv_hom_id, whiskerLeft_id (R := R)]

@[simp] theorem hom_inv_whiskerRight {f g : a ⟶ b} (e : f ≅ g) (h : b ⟶ c) :
    e.hom ▷ h ≫ e.inv ▷ h = 𝟙 (f ≫ h) := by
  rw [← comp_whiskerRight (R := R), e.hom_inv_id, id_whiskerRight (R := R)]

@[simp] theorem inv_hom_whiskerRight {f g : a ⟶ b} (e : f ≅ g) (h : b ⟶ c) :
    e.inv ▷ h ≫ e.hom ▷ h = 𝟙 (g ≫ h) := by
  rw [← comp_whiskerRight (R := R), e.inv_hom_id, id_whiskerRight (R := R)]

@[simp] theorem whiskerLeft_zero (f : a ⟶ b) (g h : b ⟶ c) : f ◁ (0 : g ⟶ h) = 0 := by
  rw [← zero_smul R (0 : g ⟶ h), whiskerLeft_smul, zero_smul]

@[simp] theorem zero_whiskerRight (f g : a ⟶ b) (h : b ⟶ c) : (0 : f ⟶ g) ▷ h = 0 := by
  rw [← zero_smul R (0 : f ⟶ g), smul_whiskerRight, zero_smul]

@[simp] theorem whiskerLeft_neg (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) : f ◁ (-η) = -(f ◁ η) := by
  rw [← neg_one_smul R η, whiskerLeft_smul, neg_one_smul]

@[simp] theorem neg_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : (-η) ▷ h = -(η ▷ h) := by
  rw [← neg_one_smul R η, smul_whiskerRight, neg_one_smul]

theorem whiskerLeft_zsmul (f : a ⟶ b) {g h : b ⟶ c} (n : ℤ) (η : g ⟶ h) :
    f ◁ (n • η) = n • (f ◁ η) := by
  rw [← Int.cast_smul_eq_zsmul R, whiskerLeft_smul, Int.cast_smul_eq_zsmul]

theorem zsmul_whiskerRight {f g : a ⟶ b} (n : ℤ) (η : f ⟶ g) (h : b ⟶ c) :
    (n • η) ▷ h = n • (η ▷ h) := by
  rw [← Int.cast_smul_eq_zsmul R, smul_whiskerRight, Int.cast_smul_eq_zsmul]

end Naturality

/-- Left whiskering of an isomorphism of 1-morphisms. -/
@[simps]
def whiskerLeftIso (f : a ⟶ b) {g h : b ⟶ c} (e : g ≅ h) : f ≫ g ≅ f ≫ h where
  hom := f ◁ e.hom
  inv := f ◁ e.inv
  hom_inv_id := whiskerLeft_hom_inv R f e
  inv_hom_id := whiskerLeft_inv_hom R f e

/-- Right whiskering of an isomorphism of 1-morphisms. -/
@[simps]
def whiskerRightIso {f g : a ⟶ b} (e : f ≅ g) (h : b ⟶ c) : f ≫ h ≅ g ≫ h where
  hom := e.hom ▷ h
  inv := e.inv ▷ h
  hom_inv_id := hom_inv_whiskerRight R e h
  inv_hom_id := inv_hom_whiskerRight R e h

/-! ### Transported coherence lemmas -/

variable (R) in
include R in
theorem unitors_equal (a : B) : (leftUnitor (𝟙 a)).hom = (rightUnitor (𝟙 a)).hom :=
  congrArg Subtype.val (Bicategory.unitors_equal (B := Underlying2 R B) (a := ⟨a⟩))

variable (R) in
include R in
theorem unitors_inv_equal (a : B) : (leftUnitor (𝟙 a)).inv = (rightUnitor (𝟙 a)).inv :=
  congrArg Subtype.val (Bicategory.unitors_inv_equal (B := Underlying2 R B) (a := ⟨a⟩))

variable (R) in
include R in
theorem leftUnitor_comp (f : a ⟶ b) (g : b ⟶ c) :
    (leftUnitor (f ≫ g)).hom = (associator (𝟙 a) f g).inv ≫ (leftUnitor f).hom ▷ g :=
  congrArg Subtype.val
    (Bicategory.leftUnitor_comp (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
theorem leftUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
    (leftUnitor (f ≫ g)).inv = (leftUnitor f).inv ▷ g ≫ (associator (𝟙 a) f g).hom :=
  congrArg Subtype.val
    (Bicategory.leftUnitor_comp_inv (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩)
      (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
theorem rightUnitor_comp (f : a ⟶ b) (g : b ⟶ c) :
    (rightUnitor (f ≫ g)).hom = (associator f g (𝟙 c)).hom ≫ f ◁ (rightUnitor g).hom :=
  congrArg Subtype.val
    (Bicategory.rightUnitor_comp (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩)
      (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
theorem rightUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
    (rightUnitor (f ≫ g)).inv = f ◁ (rightUnitor g).inv ≫ (associator f g (𝟙 c)).inv :=
  congrArg Subtype.val
    (Bicategory.rightUnitor_comp_inv (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩)
      (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
theorem leftUnitor_whiskerRight (f : a ⟶ b) (g : b ⟶ c) :
    (leftUnitor f).hom ▷ g = (associator (𝟙 a) f g).hom ≫ (leftUnitor (f ≫ g)).hom :=
  congrArg Subtype.val
    (Bicategory.leftUnitor_whiskerRight (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩)
      (c := ⟨c⟩) (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
theorem whiskerLeft_rightUnitor (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (rightUnitor g).hom = (associator f g (𝟙 c)).inv ≫ (rightUnitor (f ≫ g)).hom :=
  congrArg Subtype.val
    (Bicategory.whiskerLeft_rightUnitor (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩)
      (c := ⟨c⟩) (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
@[reassoc]
theorem pentagon_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    f ◁ (associator g h i).inv ≫ (associator f (g ≫ h) i).inv ≫ (associator f g h).inv ▷ i =
      (associator f g (h ≫ i)).inv ≫ (associator (f ≫ g) h i).inv :=
  congrArg Subtype.val
    (Bicategory.pentagon_inv (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩)
      (d := ⟨d⟩) (e := ⟨e⟩) (Underlying2.hom1 f) (Underlying2.hom1 g) (Underlying2.hom1 h) (Underlying2.hom1 i))

end TwoSupercategory

end StringDiagrams

end
