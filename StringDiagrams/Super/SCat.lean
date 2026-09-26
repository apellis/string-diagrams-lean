import StringDiagrams.Super.FunctorCategory
import StringDiagrams.Super.Bicategory
import StringDiagrams.Super.Pi

/-!
# The strict 2-supercategories `𝔖ℭ𝔞𝔱` and `Π-𝔖ℭ𝔞𝔱`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Section 2 (after Definition 2.1) and Section 3 (before Lemma 3.2).

`SCat R` is the type of (small, in fixed universes) supercategories over `R`: an `R`-linear
category with a supercategory structure (`StringDiagrams.Supercategory`). It is a strict
2-supercategory (in the unpacked form `TwoSupercategory` of Definition 2.2(i), with
`BicategoryStruct.Strict`, i.e. Definition 2.1):

* the morphism supercategories are the supercategories `ℋom(A, B)` of superfunctors and
  supernatural transformations (`Supercategory.Superfunctor R A B`, Example 1.2(iv));
* horizontal composition of 1-morphisms is composition of superfunctors (`G F := G ∘ F`, in
  diagrammatic order `F ≫ G`);
* horizontal composition of supernatural transformations is
  `(yx)_λ := y_{Hλ} ∘ G x_λ` (`Superfunctor.hcomp`), obtained from the whiskerings
  `Superfunctor.whiskerLeft` and `Superfunctor.whiskerRight`;
* the associator and unitors are identities, and the super interchange law is
  `Superfunctor.whisker_exchange`.

`PiSCat R` is the type of Π-supercategories (Definition 1.7). With superfunctors and
supernatural transformations it is the strict 2-supercategory `Π-𝔖ℭ𝔞𝔱`; its Π-2-supercategory
structure (Definition 3.1) is in `StringDiagrams.Super.PiTwo`.

## Main definitions

* `SCat R`, with instances `BicategoryStruct (SCat R)`, `TwoSupercategory R (SCat R)` and
  `BicategoryStruct.Strict (SCat R)`.
* `PiSCat R`, with the same instances.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w v u

variable (R : Type w) [CommRing R]

/-- A supercategory over `R` (Brundan–Ellis, Definition 1.1(i)), bundled: an `R`-linear
category `carrier` with a supercategory structure. -/
structure SCat where
  /-- The objects. -/
  carrier : Type u
  [str : Category.{v} carrier]
  [preadditive : Preadditive carrier]
  [linear : Linear R carrier]
  [super : Supercategory R carrier]

namespace SCat

attribute [instance] str preadditive linear super

variable {R}

instance : CoeSort (SCat.{w, v, u} R) (Type u) := ⟨SCat.carrier⟩

variable (R) in
/-- The bundled supercategory of a supercategory. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C] :
    SCat.{w, v, u} R :=
  ⟨C⟩

/-- The horizontal composition data of `𝔖ℭ𝔞𝔱`: superfunctors, supernatural transformations,
their whiskerings, and identity coherence maps. -/
instance : BicategoryStruct.{max u v, max u v} (SCat.{w, v, u} R) where
  Hom A B := Superfunctor R A B
  id A := Superfunctor.id R A
  comp F G := F.comp G
  homCategory _ _ := inferInstance
  whiskerLeft F _ _ y := Superfunctor.whiskerLeft F y
  whiskerRight x G := Superfunctor.whiskerRight x G
  associator F G H := Iso.refl (F.comp (G.comp H))
  leftUnitor F := Iso.refl F
  rightUnitor F := Iso.refl F

instance (A B : SCat.{w, v, u} R) : Preadditive (A ⟶ B) :=
  inferInstanceAs (Preadditive (Superfunctor R A B))

instance (A B : SCat.{w, v, u} R) : Linear R (A ⟶ B) :=
  inferInstanceAs (Linear R (Superfunctor R A B))

instance (A B : SCat.{w, v, u} R) : Supercategory R (A ⟶ B) :=
  inferInstanceAs (Supercategory R (Superfunctor R A B))

open BicategoryStruct

theorem hom_def (A B : SCat.{w, v, u} R) : (A ⟶ B) = Superfunctor R A B := rfl

theorem comp_def {A B C : SCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) : F ≫ G = F.comp G := rfl

theorem id_def (A : SCat.{w, v, u} R) : 𝟙 A = Superfunctor.id R A := rfl

theorem whiskerLeft_def {A B C : SCat.{w, v, u} R} (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) :
    F ◁ y = Superfunctor.whiskerLeft F y := rfl

theorem whiskerRight_def {A B C : SCat.{w, v, u} R} {F H : A ⟶ B} (x : F ⟶ H) (G : B ⟶ C) :
    x ▷ G = Superfunctor.whiskerRight x G := rfl

@[simp] theorem associator_hom {A B C D : SCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).hom = 𝟙 (F ≫ G ≫ H) := rfl

@[simp] theorem associator_inv {A B C D : SCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).inv = 𝟙 (F ≫ G ≫ H) := rfl

@[simp] theorem leftUnitor_hom {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).hom = 𝟙 F := rfl

@[simp] theorem leftUnitor_inv {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).inv = 𝟙 F := rfl

@[simp] theorem rightUnitor_hom {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).hom = 𝟙 F := rfl

@[simp] theorem rightUnitor_inv {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).inv = 𝟙 F := rfl


section App

variable {A B C : SCat.{w, v, u} R}

@[simp] theorem comp_app_zero {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 0 X = x.app 0 X ≫ y.app 0 X + x.app 1 X ≫ y.app 1 X :=
  Superfunctor.comp_app_zero x y X

@[simp] theorem comp_app_one {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 1 X = x.app 0 X ≫ y.app 1 X + x.app 1 X ≫ y.app 0 X :=
  Superfunctor.comp_app_one x y X

theorem comp_app {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (r : ZMod 2) (X : A.carrier) :
    (x ≫ y).app r X = x.app 0 X ≫ y.app r X + x.app 1 X ≫ y.app (r + 1) X := rfl

@[simp] theorem id_app_zero (F : A ⟶ B) (X : A.carrier) :
    (𝟙 F : F ⟶ F).app 0 X = 𝟙 (F.obj X) := rfl

@[simp] theorem id_app_one (F : A ⟶ B) (X : A.carrier) : (𝟙 F : F ⟶ F).app 1 X = 0 := rfl

@[simp] theorem add_app {F G : A ⟶ B} (x y : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (x + y).app p X = x.app p X + y.app p X := rfl

@[simp] theorem neg_app {F G : A ⟶ B} (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (-x).app p X = -x.app p X := rfl

@[simp] theorem smul_app {F G : A ⟶ B} (r : R) (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (r • x).app p X = r • x.app p X := rfl

@[simp] theorem zero_app {F G : A ⟶ B} (p : ZMod 2) (X : A.carrier) :
    (0 : F ⟶ G).app p X = 0 := rfl

@[simp] theorem whiskerLeft_app (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) (p : ZMod 2)
    (X : A.carrier) : (F ◁ y).app p X = y.app p (F.obj X) := rfl

@[simp] theorem whiskerRight_app {F H : A ⟶ B} (x : F ⟶ H) (G : B ⟶ C) (p : ZMod 2)
    (X : A.carrier) : (x ▷ G).app p X = G.map (x.app p X) := rfl

@[simp] theorem comp_obj (F : A ⟶ B) (G : B ⟶ C) (X : A.carrier) :
    Superfunctor.obj (F ≫ G) X = G.obj (F.obj X) := rfl

@[simp] theorem comp_map (F : A ⟶ B) (G : B ⟶ C) {X Y : A.carrier} (f : X ⟶ Y) :
    Superfunctor.map (F ≫ G) f = G.map (F.map f) := rfl

@[simp] theorem id_obj (X : A.carrier) : Superfunctor.obj (𝟙 A) X = X := rfl

@[simp] theorem id_map {X Y : A.carrier} (f : X ⟶ Y) : Superfunctor.map (𝟙 A) f = f := rfl

theorem hom_ext {F G : A ⟶ B} {x y : F ⟶ G} (h0 : ∀ X, x.app 0 X = y.app 0 X)
    (h1 : ∀ X, x.app 1 X = y.app 1 X) : x = y :=
  Superfunctor.hom_ext_parity h0 h1

end App

/-- **Brundan–Ellis, Section 2.** Supercategories, superfunctors and supernatural
transformations form a 2-supercategory `𝔖ℭ𝔞𝔱`. -/
instance : TwoSupercategory R (SCat.{w, v, u} R) where
  whiskerLeft_id F G := Superfunctor.whiskerLeft_id F G
  whiskerLeft_comp F _ _ _ y z := Superfunctor.whiskerLeft_comp F y z
  id_whiskerLeft y := by
    rw [leftUnitor_hom, leftUnitor_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  comp_whiskerLeft F G _ _ y := by
    rw [associator_hom, associator_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  id_whiskerRight F G := Superfunctor.id_whiskerRight F G
  comp_whiskerRight x z G := Superfunctor.comp_whiskerRight x z G
  whiskerRight_id x := by
    rw [rightUnitor_hom, rightUnitor_inv]; erw [Category.id_comp, Category.comp_id]
    exact Superfunctor.hom_ext fun _ _ => rfl
  whiskerRight_comp x G H := by
    rw [associator_hom, associator_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  whisker_assoc F _ _ y H := by
    rw [associator_hom, associator_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  pentagon F G H K := by
    simp only [associator_hom]; erw [Category.id_comp]
    change Superfunctor.whiskerRight (𝟙 (F.comp (G.comp H))) K ≫
      Superfunctor.whiskerLeft F (𝟙 (G.comp (H.comp K))) =
      Superfunctor.whiskerLeft F (𝟙 (G.comp (H.comp K)))
    rw [Superfunctor.id_whiskerRight, Superfunctor.whiskerLeft_id, Category.id_comp]
  triangle F G := by
    simp only [associator_hom, leftUnitor_hom, rightUnitor_hom]; erw [Category.id_comp]
    exact (Superfunctor.whiskerLeft_id F G).trans (Superfunctor.id_whiskerRight F G).symm
  whiskerLeft_add F _ _ y z := Superfunctor.whiskerLeft_add F y z
  add_whiskerRight x z G := Superfunctor.add_whiskerRight x z G
  whiskerLeft_smul F _ _ r y := Superfunctor.whiskerLeft_smul F r y
  smul_whiskerRight r x G := Superfunctor.smul_whiskerRight r x G
  whiskerLeft_mem F _ _ _ _ hy := Superfunctor.whiskerLeft_mem F hy
  whiskerRight_mem G hx := Superfunctor.whiskerRight_mem hx G
  super_interchange hx hy := Superfunctor.whisker_exchange hx hy
  associator_hom_mem _ _ _ := id_mem _
  leftUnitor_hom_mem _ := id_mem _
  rightUnitor_hom_mem _ := id_mem _

/-- **Brundan–Ellis, Section 2.** `𝔖ℭ𝔞𝔱` is a strict 2-supercategory (Definition 2.1). -/
instance : BicategoryStruct.Strict (SCat.{w, v, u} R) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

end SCat

/-! ## Π-supercategories -/

/-- A Π-supercategory over `R` (Brundan–Ellis, Definition 1.7), bundled. -/
structure PiSCat extends SCat.{w, v, u} R where
  [pi : PiSupercategory R carrier]

namespace PiSCat

attribute [instance] pi

variable {R}

instance : CoeSort (PiSCat.{w, v, u} R) (Type u) := ⟨fun A => A.carrier⟩

variable (R) in
/-- The bundled Π-supercategory of a Π-supercategory. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]
    [PiSupercategory R C] : PiSCat.{w, v, u} R :=
  ⟨SCat.of R C⟩

open BicategoryStruct

/-- The data of the 2-supercategory `Π-𝔖ℭ𝔞𝔱` of Π-supercategories, superfunctors and
supernatural transformations: that of `𝔖ℭ𝔞𝔱` on the underlying supercategories. -/
instance : BicategoryStruct.{max u v, max u v} (PiSCat.{w, v, u} R) where
  Hom A B := A.toSCat ⟶ B.toSCat
  id A := 𝟙 A.toSCat
  comp F G := F ≫ G
  homCategory A B := inferInstanceAs (Category (A.toSCat ⟶ B.toSCat))
  whiskerLeft F _ _ y := F ◁ y
  whiskerRight x G := x ▷ G
  associator F G H := associator (B := SCat R) F G H
  leftUnitor F := leftUnitor (B := SCat R) F
  rightUnitor F := rightUnitor (B := SCat R) F

instance (A B : PiSCat.{w, v, u} R) : Preadditive (A ⟶ B) :=
  inferInstanceAs (Preadditive (A.toSCat ⟶ B.toSCat))

instance (A B : PiSCat.{w, v, u} R) : Linear R (A ⟶ B) :=
  inferInstanceAs (Linear R (A.toSCat ⟶ B.toSCat))

instance (A B : PiSCat.{w, v, u} R) : Supercategory R (A ⟶ B) :=
  inferInstanceAs (Supercategory R (A.toSCat ⟶ B.toSCat))

theorem hom_def (A B : PiSCat.{w, v, u} R) : (A ⟶ B) = Superfunctor R A B := rfl

theorem comp_def {A B C : PiSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) :
    F ≫ G = Superfunctor.comp F G := rfl

theorem id_def (A : PiSCat.{w, v, u} R) : 𝟙 A = Superfunctor.id R A := rfl

theorem whiskerLeft_def {A B C : PiSCat.{w, v, u} R} (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) :
    F ◁ y = Superfunctor.whiskerLeft F y := rfl

theorem whiskerRight_def {A B C : PiSCat.{w, v, u} R} {F H : A ⟶ B} (x : F ⟶ H)
    (G : B ⟶ C) : x ▷ G = Superfunctor.whiskerRight x G := rfl


section App

variable {A B C : PiSCat.{w, v, u} R}

@[simp] theorem comp_app_zero {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 0 X = x.app 0 X ≫ y.app 0 X + x.app 1 X ≫ y.app 1 X :=
  Superfunctor.comp_app_zero x y X

@[simp] theorem comp_app_one {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 1 X = x.app 0 X ≫ y.app 1 X + x.app 1 X ≫ y.app 0 X :=
  Superfunctor.comp_app_one x y X

theorem comp_app {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (r : ZMod 2) (X : A.carrier) :
    (x ≫ y).app r X = x.app 0 X ≫ y.app r X + x.app 1 X ≫ y.app (r + 1) X := rfl

@[simp] theorem id_app_zero (F : A ⟶ B) (X : A.carrier) :
    (𝟙 F : F ⟶ F).app 0 X = 𝟙 (F.obj X) := rfl

@[simp] theorem id_app_one (F : A ⟶ B) (X : A.carrier) : (𝟙 F : F ⟶ F).app 1 X = 0 := rfl

@[simp] theorem add_app {F G : A ⟶ B} (x y : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (x + y).app p X = x.app p X + y.app p X := rfl

@[simp] theorem neg_app {F G : A ⟶ B} (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (-x).app p X = -x.app p X := rfl

@[simp] theorem smul_app {F G : A ⟶ B} (r : R) (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (r • x).app p X = r • x.app p X := rfl

@[simp] theorem zero_app {F G : A ⟶ B} (p : ZMod 2) (X : A.carrier) :
    (0 : F ⟶ G).app p X = 0 := rfl

@[simp] theorem whiskerLeft_app (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) (p : ZMod 2)
    (X : A.carrier) : (F ◁ y).app p X = y.app p (F.obj X) := rfl

@[simp] theorem whiskerRight_app {F H : A ⟶ B} (x : F ⟶ H) (G : B ⟶ C) (p : ZMod 2)
    (X : A.carrier) : (x ▷ G).app p X = G.map (x.app p X) := rfl

@[simp] theorem comp_obj (F : A ⟶ B) (G : B ⟶ C) (X : A.carrier) :
    Superfunctor.obj (F ≫ G) X = G.obj (F.obj X) := rfl

@[simp] theorem comp_map (F : A ⟶ B) (G : B ⟶ C) {X Y : A.carrier} (f : X ⟶ Y) :
    Superfunctor.map (F ≫ G) f = G.map (F.map f) := rfl

@[simp] theorem id_obj (X : A.carrier) : Superfunctor.obj (𝟙 A) X = X := rfl

@[simp] theorem id_map {X Y : A.carrier} (f : X ⟶ Y) : Superfunctor.map (𝟙 A) f = f := rfl

theorem hom_ext {F G : A ⟶ B} {x y : F ⟶ G} (h0 : ∀ X, x.app 0 X = y.app 0 X)
    (h1 : ∀ X, x.app 1 X = y.app 1 X) : x = y :=
  Superfunctor.hom_ext_parity h0 h1

end App

/-- **Brundan–Ellis, Section 3.** Π-supercategories, superfunctors and supernatural
transformations form a 2-supercategory `Π-𝔖ℭ𝔞𝔱`. -/
instance : TwoSupercategory R (PiSCat.{w, v, u} R) where
  whiskerLeft_id F G := TwoSupercategory.whiskerLeft_id (R := R) (B := SCat R) F G
  whiskerLeft_comp F _ _ _ y z := TwoSupercategory.whiskerLeft_comp (R := R) (B := SCat R) F y z
  id_whiskerLeft y := TwoSupercategory.id_whiskerLeft (R := R) (B := SCat R) y
  comp_whiskerLeft F G _ _ y := TwoSupercategory.comp_whiskerLeft (R := R) (B := SCat R) F G y
  id_whiskerRight F G := TwoSupercategory.id_whiskerRight (R := R) (B := SCat R) F G
  comp_whiskerRight x z G := TwoSupercategory.comp_whiskerRight (R := R) (B := SCat R) x z G
  whiskerRight_id x := TwoSupercategory.whiskerRight_id (R := R) (B := SCat R) x
  whiskerRight_comp x G H := TwoSupercategory.whiskerRight_comp (R := R) (B := SCat R) x G H
  whisker_assoc F _ _ y H := TwoSupercategory.whisker_assoc (R := R) (B := SCat R) F y H
  pentagon F G H K := TwoSupercategory.pentagon (R := R) (B := SCat R) F G H K
  triangle F G := TwoSupercategory.triangle (R := R) (B := SCat R) F G
  whiskerLeft_add F _ _ y z := TwoSupercategory.whiskerLeft_add (R := R) (B := SCat R) F y z
  add_whiskerRight x z G := TwoSupercategory.add_whiskerRight (R := R) (B := SCat R) x z G
  whiskerLeft_smul F _ _ r y := TwoSupercategory.whiskerLeft_smul (B := SCat R) F r y
  smul_whiskerRight r x G := TwoSupercategory.smul_whiskerRight (B := SCat R) r x G
  whiskerLeft_mem F _ _ _ _ hy := TwoSupercategory.whiskerLeft_mem (B := SCat R) F hy
  whiskerRight_mem G hx := TwoSupercategory.whiskerRight_mem (B := SCat R) G hx
  super_interchange hx hy := TwoSupercategory.super_interchange (B := SCat R) hx hy
  associator_hom_mem F G H := TwoSupercategory.associator_hom_mem (B := SCat R) F G H
  leftUnitor_hom_mem F := TwoSupercategory.leftUnitor_hom_mem (B := SCat R) F
  rightUnitor_hom_mem F := TwoSupercategory.rightUnitor_hom_mem (B := SCat R) F

@[simp] theorem associator_hom {A B C D : PiSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).hom = 𝟙 (F ≫ G ≫ H) := rfl

@[simp] theorem associator_inv {A B C D : PiSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).inv = 𝟙 (F ≫ G ≫ H) := rfl

@[simp] theorem leftUnitor_hom {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).hom = 𝟙 F := rfl

@[simp] theorem leftUnitor_inv {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).inv = 𝟙 F := rfl

@[simp] theorem rightUnitor_hom {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).hom = 𝟙 F := rfl

@[simp] theorem rightUnitor_inv {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).inv = 𝟙 F := rfl

/-- `Π-𝔖ℭ𝔞𝔱` is a strict 2-supercategory. -/
instance : BicategoryStruct.Strict (PiSCat.{w, v, u} R) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

end PiSCat

end StringDiagrams

end
