import StringDiagrams.Super.AssociatedTwoNatEquiv
import StringDiagrams.Super.DrinfeldCenter
import StringDiagrams.Super.QPiTwoSCat
import StringDiagrams.Super.MonoidalPi
import Mathlib.CategoryTheory.Bicategory.End
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Remark 5.7: the Drinfeld center of a Π-2-supercategory and its underlying Π-2-category

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Remark 5.7.
The remark deduces from the 3-categorical version of Theorem 5.5 that the monoidal category
underlying the Drinfeld center of a Π-2-supercategory `𝔄` is monoidally equivalent to the Drinfeld
center of `𝔄̲`. The endomorphisms of the identity in the 3-category of Π-2-categories are the
strong *Π-2-natural* transformations of the identity, so the target is the Π-center of `𝔄̲`
(strong transformations of the identity satisfying the axiom of Definition 5.2(iii)), not its
full Drinfeld center; for the latter the statement fails
(`StringDiagrams.Super.DrinfeldCenterPiCounterexample` and the README erratum).

* `Center2 C`: the Drinfeld center (Definition 2.3) of a 2-category `C`, the full monoidal
  subcategory of `(End 𝕀)ᴹᵒᵖ` (in the bicategory of oplax functors) on the strong
  transformations, so that `(X ⊗ Y)_λ = X_λ Y_λ`.
* `PiCenter R C`: for a Π-2-category, the full monoidal subcategory on the transformations
  which are moreover Π-2-natural for the identity Π-2-functor.
* `DrinfeldCenter.toPiCenter`: the comparison functor `Z(𝔄)̲ → Z_Π(𝔄̲)`, `(X, x) ↦ 𝔼₂(X, x)`;
  it is faithful, full (a modification has even components), surjective on objects (a
  Π-2-natural transformation of the identity of `𝔄̲` is natural with respect to all
  2-morphisms of `𝔄`, `TwoNatTrans.ofPiTwoNatural`), and monoidal with identity coherence
  isomorphisms (`DrinfeldCenter.toPiCenterCoreMonoidal`); `DrinfeldCenter.centerEquivalence`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory MonoidalCategory Supercategory
open scoped Oplax.OplaxTrans Oplax.OplaxTrans.OplaxFunctor

universe w w₁ v₁ u₁

/-! ## The Drinfeld center and the Π-center of a 2-category -/

section Center

variable (C : Type u₁) [Bicategory.{w₁, v₁} C]

/-- The oplax transformations of the identity of a bicategory, with the monoidal structure of
endomorphisms in the bicategory of oplax functors, opposite (so that `(X ⊗ Y)_λ = X_λ Y_λ`,
i.e. `Y_λ ≫ X_λ`, as in Definition 2.3). -/
abbrev EndIdOp := (EndMonoidal (OplaxFunctor.id C))ᴹᵒᵖ

variable {C}

/-- An oplax transformation is strong if its naturality 2-morphisms are invertible. -/
def IsStrongOplax {F G : C ⥤ᵒᵖᴸ C} (η : F ⟶ G) : Prop :=
  ∀ {a b : C} (f : a ⟶ b), IsIso (η.naturality f)

theorem isStrongOplax_id (F : C ⥤ᵒᵖᴸ C) : IsStrongOplax (𝟙 F) := fun f => by
  change IsIso ((Bicategory.rightUnitor (F.map f)).hom ≫ (Bicategory.leftUnitor (F.map f)).inv)
  infer_instance

theorem IsStrongOplax.comp {F G H : C ⥤ᵒᵖᴸ C} {η : F ⟶ G} {θ : G ⟶ H} (hη : IsStrongOplax η)
    (hθ : IsStrongOplax θ) : IsStrongOplax (η ≫ θ) := fun {a b} f => by
  have := hη f
  have := hθ f
  change IsIso ((Bicategory.associator (F.map f) (η.app b) (θ.app b)).inv ≫
    Bicategory.whiskerRight (η.naturality f) (θ.app b) ≫
    (Bicategory.associator (η.app a) (G.map f) (θ.app b)).hom ≫
      Bicategory.whiskerLeft (η.app a) (θ.naturality f) ≫
      (Bicategory.associator (η.app a) (θ.app a) (H.map f)).inv)
  infer_instance

variable (C) in
/-- The objects of the Drinfeld center of a 2-category: strong transformations of the
identity. -/
def centerProp : ObjectProperty (EndIdOp C) := fun X => IsStrongOplax X.unmop

instance : (centerProp C).IsMonoidal where
  prop_unit := isStrongOplax_id _
  prop_tensor {_ _} hX hY := IsStrongOplax.comp hY hX

variable (C) in
/-- **Brundan–Ellis, Definition 2.3**, for a 2-category `C` (all 2-morphisms even): the
Drinfeld center, the monoidal category of strong transformations `𝕀 ⇒ 𝕀` and modifications,
with `(X ⊗ Y)_λ = X_λ Y_λ`. -/
abbrev Center2 := (centerProp C).FullSubcategory

end Center

section PiCenter

variable (R : Type w) [CommRing R] (C : Type u₁) [Bicategory.{w₁, v₁} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [PiTwoCategory R C]

/-- The objects of the Π-center of a Π-2-category: strong transformations of the identity
which are Π-2-natural (Definition 5.2(iii)) as transformations of the identity Π-2-functor. -/
def piCenterProp : ObjectProperty (EndIdOp C) := fun X =>
  IsStrongOplax X.unmop ∧ (PiTwoFunctor.id R C).IsPiTwoNatural (PiTwoFunctor.id R C) X.unmop

instance : (piCenterProp R C).IsMonoidal where
  prop_unit := ⟨isStrongOplax_id _, PiTwoFunctor.isPiTwoNatural_id (PiTwoFunctor.id R C)⟩
  prop_tensor {_ _} hX hY := ⟨IsStrongOplax.comp hY.1 hX.1, hY.2.vcomp hX.2⟩

/-- The Π-center of a Π-2-category: the full monoidal subcategory of the Drinfeld center on
the Π-2-natural transformations of the identity Π-2-functor. These are the
endomorphisms of the identity in the 3-category of Π-2-categories, Π-2-functors,
Π-2-natural transformations and modifications of Remark 5.7. -/
abbrev PiCenter := (piCenterProp R C).FullSubcategory

end PiCenter

/-! ## The comparison functor `Z(𝔄)̲ → Z_Π(𝔄̲)` -/

section Comparison

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B] [PiTwoSupercategory R B]

namespace TwoNatTrans

/-- The `j` of the identity 2-superfunctor (5.4) is the identity. -/
theorem id_toPiTwoFunctor_j_hom (a : Underlying2 R B) :
    ((TwoSuperfunctor.id R B).toPiTwoFunctor.j a).hom = 𝟙 _ :=
  Subtype.ext (TwoSuperfunctor.jIso_id_hom (R := R) a.obj)

/-- Π-2-naturality for the identity Π-2-functor of `𝔄̲` is Π-2-naturality for `E₂ 𝕀`. -/
theorem isPiTwoNatural_id_iff (η : idU R B ⟶ idU R B) :
    (PiTwoFunctor.id R (Underlying2 R B)).IsPiTwoNatural (PiTwoFunctor.id R _) η ↔
      (TwoSuperfunctor.id R B).toPiTwoFunctor.IsPiTwoNatural
        (TwoSuperfunctor.id R B).toPiTwoFunctor η := by
  refine forall_congr' fun a => ?_
  rw [id_toPiTwoFunctor_j_hom, PiTwoFunctor.id_j, Iso.refl_hom]
  rfl

/-- `𝔼₂` of a 2-natural transformation of the identity is Π-2-natural for the identity
Π-2-functor of `𝔄̲`. -/
theorem isPiTwoNatural_toOplax (θ : EndId R B) :
    (PiTwoFunctor.id R (Underlying2 R B)).IsPiTwoNatural (PiTwoFunctor.id R _) θ.toOplax :=
  (isPiTwoNatural_id_iff θ.toOplax).2 θ.isPiTwoNatural

/-- The modification of `𝔼₂` of an even supermodification. -/
@[simps]
def modOfEven {θ θ' : EndId R B} (g : θ ⟶ θ') (hg : g ∈ parity (R := R) θ θ' 0) :
    Oplax.OplaxTrans.Modification θ.toOplax θ'.toOplax where
  app a := ⟨g.app a.obj, hg a.obj⟩
  naturality f := Subtype.ext (g.naturality f.obj).symm

end TwoNatTrans

namespace DrinfeldCenter

open TwoNatTrans

omit [PiTwoSupercategory R B] in
theorem toOplax_isStrong (X : DrinfeldCenter R B) : IsStrongOplax X.toTwoNatTrans.toOplax :=
  fun {a b} f => by
    have := X.isStrong f.obj
    let Xa : a.obj ⟶ a.obj := X.toTwoNatTrans.X a.obj
    let Xb : b.obj ⟶ b.obj := X.toTwoNatTrans.X b.obj
    let e : f.obj ≫ Xb ≅ Xa ≫ f.obj := asIso (X.toTwoNatTrans.x f.obj)
    have hm : e.hom ∈ parity (R := R) (f.obj ≫ Xb) (Xa ≫ f.obj) 0 :=
      X.toTwoNatTrans.x_mem f.obj
    exact ⟨⟨⟨e.inv, Supercategory.inv_mem (R := R) (C := a.obj ⟶ b.obj) e hm⟩,
      Subtype.ext e.hom_inv_id, Subtype.ext e.inv_hom_id⟩⟩

variable (R B) in
/-- **Remark 5.7.** The comparison functor from the underlying monoidal category of the Drinfeld
center of a Π-2-supercategory `𝔄` to the Π-center of `𝔄̲ = E₂ 𝔄`: `(X, x) ↦ (X, x)` (`𝔼₂`),
even supermodifications to modifications. -/
@[simps obj]
def toPiCenter : Underlying R (DrinfeldCenter R B) ⥤ PiCenter R (Underlying2 R B) where
  obj X := ⟨MonoidalOpposite.mop X.obj.toTwoNatTrans.toOplax,
    toOplax_isStrong X.obj, isPiTwoNatural_toOplax X.obj.toTwoNatTrans⟩
  map {_ _} g := ObjectProperty.homMk (Quiver.Hom.mop ⟨modOfEven g.1 g.2⟩)
  map_id _ := ObjectProperty.hom_ext _ (Quiver.Hom.unmop_inj
    (Oplax.OplaxTrans.homCategory.ext fun _ => rfl))
  map_comp _ _ := ObjectProperty.hom_ext _ (Quiver.Hom.unmop_inj
    (Oplax.OplaxTrans.homCategory.ext fun _ => rfl))

@[simp] theorem toPiCenter_map_app {X Y : Underlying R (DrinfeldCenter R B)} (g : X ⟶ Y)
    (a : Underlying2 R B) :
    (((toPiCenter R B).map g).hom.unmop.as.app a).1 = g.1.app a.obj := rfl

/-- The functor `toPiCenter` is faithful: even supermodifications are determined by their
components. -/
instance : (toPiCenter R B).Faithful where
  map_injective {X Y} _ _ h := Subtype.ext (TwoNatTrans.hom_ext fun a =>
    congrArg (fun k : (toPiCenter R B).obj X ⟶ (toPiCenter R B).obj Y =>
      (k.hom.unmop.as.app ⟨a⟩).1) h)

/-- The functor `toPiCenter` is full: a modification has even components. -/
instance : (toPiCenter R B).Full where
  map_surjective {_ _} k := ⟨⟨TwoNatTrans.homOfModification k.hom.unmop.as,
      fun a => (k.hom.unmop.as.app ⟨a⟩).2⟩,
    ObjectProperty.hom_ext _ (Quiver.Hom.unmop_inj
      (Oplax.OplaxTrans.homCategory.ext fun _ => rfl))⟩

/-- An object of the Π-center, as an object of the Drinfeld center of `𝔄`: a Π-2-natural
transformation of the identity of `𝔄̲` is natural with respect to all 2-morphisms of `𝔄`
(`TwoNatTrans.ofPiTwoNatural`). -/
def ofPiCenter (Z : PiCenter R (Underlying2 R B)) : DrinfeldCenter R B where
  toTwoNatTrans := TwoNatTrans.ofPiTwoNatural (F := TwoSuperfunctor.id R B)
    (G := TwoSuperfunctor.id R B) Z.obj.unmop ((isPiTwoNatural_id_iff Z.obj.unmop).1 Z.property.2)
  isStrong {a b} f := by
    have h := Z.property.1 (Underlying2.hom1 (R := R) f)
    exact @Functor.map_isIso _ _ _ _ (F := Underlying.ι R (a ⟶ b)) _ _ _ h

/-- The functor `toPiCenter` is surjective on objects. -/
theorem toPiCenter_obj_ofPiCenter (Z : PiCenter R (Underlying2 R B)) :
    (toPiCenter R B).obj ⟨ofPiCenter Z⟩ = Z := rfl

instance : (toPiCenter R B).EssSurj where
  mem_essImage Z := ⟨⟨ofPiCenter Z⟩, ⟨eqToIso (toPiCenter_obj_ofPiCenter Z)⟩⟩

instance : (toPiCenter R B).IsEquivalence where

/-- Morphisms of the Π-center are determined by their components. -/
theorem piCenter_hom_ext {X Y : PiCenter R (Underlying2 R B)} {k k' : X ⟶ Y}
    (h : ∀ a : B, (k.hom.unmop.as.app ⟨a⟩).1 = (k'.hom.unmop.as.app ⟨a⟩).1) : k = k' :=
  ObjectProperty.hom_ext _ (Quiver.Hom.unmop_inj
    (Oplax.OplaxTrans.homCategory.ext fun a => Subtype.ext (h a.obj)))

section PiCenterApp

variable {X Y Z : PiCenter R (Underlying2 R B)}

/-- The component in `𝔄` of a morphism of the Π-center. -/
def appB (k : X ⟶ Y) (a : B) : (X.obj.unmop.app ⟨a⟩).obj ⟶ (Y.obj.unmop.app ⟨a⟩).obj :=
  (k.hom.unmop.as.app ⟨a⟩).1

@[simp] theorem comp_appB (k : X ⟶ Y) (k' : Y ⟶ Z) (a : B) :
    appB (k ≫ k') a = appB k a ≫ appB k' a := rfl

@[simp] theorem id_appB (X : PiCenter R (Underlying2 R B)) (a : B) :
    appB (𝟙 X) a = 𝟙 _ := rfl

@[simp] theorem whiskerLeft_appB (W : PiCenter R (Underlying2 R B)) (k : X ⟶ Y) (a : B) :
    appB (W ◁ k) a =
      BicategoryStruct.whiskerRight (appB k a) (W.obj.unmop.app ⟨a⟩).obj := rfl

@[simp] theorem whiskerRight_appB (k : X ⟶ Y) (W : PiCenter R (Underlying2 R B)) (a : B) :
    appB (k ▷ W) a =
      BicategoryStruct.whiskerLeft (W.obj.unmop.app ⟨a⟩).obj (appB k a) := rfl

@[simp] theorem associator_hom_appB (X Y Z : PiCenter R (Underlying2 R B)) (a : B) :
    appB (α_ X Y Z).hom a = (BicategoryStruct.associator (Z.obj.unmop.app ⟨a⟩).obj
      (Y.obj.unmop.app ⟨a⟩).obj (X.obj.unmop.app ⟨a⟩).obj).inv := rfl

@[simp] theorem leftUnitor_hom_appB (X : PiCenter R (Underlying2 R B)) (a : B) :
    appB (λ_ X).hom a = (BicategoryStruct.rightUnitor (X.obj.unmop.app ⟨a⟩).obj).hom := rfl

@[simp] theorem rightUnitor_hom_appB (X : PiCenter R (Underlying2 R B)) (a : B) :
    appB (ρ_ X).hom a = (BicategoryStruct.leftUnitor (X.obj.unmop.app ⟨a⟩).obj).hom := rfl

@[simp] theorem toPiCenter_map_appB {X Y : Underlying R (DrinfeldCenter R B)} (g : X ⟶ Y)
    (a : B) : appB ((toPiCenter R B).map g) a = g.1.app a := rfl

end PiCenterApp

/-- **Remark 5.7.** `toPiCenter` is a monoidal functor, with identity coherence isomorphisms. -/
def toPiCenterCoreMonoidal : (toPiCenter R B).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left _ _ := piCenter_hom_ext fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm
  μIso_hom_natural_right _ _ := piCenter_hom_ext fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm
  associativity X Y Z := piCenter_hom_ext fun a => by
    change BicategoryStruct.whiskerLeft (Z.obj.toTwoNatTrans.X a)
        (𝟙 (Y.obj.toTwoNatTrans.X a ≫ X.obj.toTwoNatTrans.X a)) ≫ 𝟙 _ ≫
          (BicategoryStruct.associator (Z.obj.toTwoNatTrans.X a) (Y.obj.toTwoNatTrans.X a)
            (X.obj.toTwoNatTrans.X a)).inv =
      (BicategoryStruct.associator (Z.obj.toTwoNatTrans.X a) (Y.obj.toTwoNatTrans.X a)
          (X.obj.toTwoNatTrans.X a)).inv ≫
        BicategoryStruct.whiskerRight (𝟙 (Z.obj.toTwoNatTrans.X a ≫ Y.obj.toTwoNatTrans.X a))
          (X.obj.toTwoNatTrans.X a) ≫ 𝟙 _
    rw [TwoSupercategory.whiskerLeft_id (R := R), TwoSupercategory.id_whiskerRight (R := R)]
    simp
  left_unitality X := piCenter_hom_ext fun a => by
    change (BicategoryStruct.rightUnitor (X.obj.toTwoNatTrans.X a)).hom =
      BicategoryStruct.whiskerLeft (X.obj.toTwoNatTrans.X a) (𝟙 (𝟙 a)) ≫ 𝟙 _ ≫
        (BicategoryStruct.rightUnitor (X.obj.toTwoNatTrans.X a)).hom
    rw [TwoSupercategory.whiskerLeft_id (R := R)]
    simp
  right_unitality X := piCenter_hom_ext fun a => by
    change (BicategoryStruct.leftUnitor (X.obj.toTwoNatTrans.X a)).hom =
      BicategoryStruct.whiskerRight (𝟙 (𝟙 a)) (X.obj.toTwoNatTrans.X a) ≫ 𝟙 _ ≫
        (BicategoryStruct.leftUnitor (X.obj.toTwoNatTrans.X a)).hom
    rw [TwoSupercategory.id_whiskerRight (R := R)]
    simp

instance : (toPiCenter R B).Monoidal := toPiCenterCoreMonoidal.toMonoidal

variable (R B) in
/-- **Brundan–Ellis, Remark 5.7 (consequence, corrected).** The monoidal category underlying the
Drinfeld center of a Π-2-supercategory `𝔄` is monoidally equivalent to the Π-center of
`𝔄̲ = E₂ 𝔄` (the strong Π-2-natural transformations of the identity Π-2-functor and their
modifications), via the monoidal functor `toPiCenter`, which is bijective on objects and on
morphisms. -/
def centerEquivalence : Underlying R (DrinfeldCenter R B) ≌ PiCenter R (Underlying2 R B) :=
  (toPiCenter R B).asEquivalence

theorem centerEquivalence_functor : (centerEquivalence R B).functor = toPiCenter R B := rfl

end DrinfeldCenter

end Comparison

end StringDiagrams

end
