import StringDiagrams.Super.TwoFunctor
import StringDiagrams.Super.Monoidal
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax

/-!
# The Drinfeld center of a 2-supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 2.3 and Lemma 3.2.

The Drinfeld center of a 2-supercategory `𝔄` is the monoidal supercategory of strong
2-natural transformations `𝕀 ⇒ 𝕀` and supermodifications
(`StringDiagrams.DrinfeldCenter R B`). An object `(X, x)` is a coherent family of 1-morphisms
`X_λ : λ → λ` and even 2-isomorphisms `x_F : X_μ F ⇒ F X_λ` (in the diagrammatic order
`F ≫ X_μ ⟶ X_λ ≫ F`); a morphism is a supermodification. The tensor product is
`(X ⊗ Y)_λ := X_λ Y_λ` (i.e. `Y_λ ≫ X_λ`), `(x ⊗ y)_F := x_F y_F`, and on morphisms
`(α ⊗ β)_λ := α_λ β_λ`.

## Implementation

A 2-natural transformation `𝕀 ⇒ 𝕀` involves only even 2-morphisms, so it is the same as an
oplax transformation of the identity of the underlying bicategory `Underlying2 R B`
(Mathlib's `Oplax.OplaxTrans`; `TwoNatTrans.toOplax`, `TwoNatTrans.ofOplax`). We use this to
obtain the tensor product of objects, its coherence and the coherence isomorphisms
from Mathlib's bicategory of oplax functors. The tensor product of morphisms, which may be
odd, is defined directly, and the axioms of a monoidal supercategory
(`MonoidalSupercategory`, Definition 1.4 unpacked) are checked componentwise.

## Main definitions

* `StringDiagrams.DrinfeldCenter R B`, with instances `Category`, `Preadditive`, `Linear R`,
  `Supercategory R`, `MonoidalCategoryStruct` and `MonoidalSupercategory R`.
* `PiTwoSupercategory.centerObj`: **Lemma 3.2** — `(π, β)` is an object of the Drinfeld center.
* `PiTwoSupercategory.centerζ`: `ζ` is an odd isomorphism `(π, β) ≅ 1` in the Drinfeld center,
  and `PiTwoSupercategory.centerξ`: `ξ` is an even isomorphism `(π, β) ⊗ (π, β) ≅ 1`
  (Lemma 3.2(iv)).

## Not formalized

The braiding of the Drinfeld center (the paper omits the definition of a braided monoidal
supercategory), and the remark that the Drinfeld center of a strict 2-supercategory is strict.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w v u w₁

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-! ## 2-natural transformations of the identity as oplax transformations -/

namespace TwoNatTrans

/-- The 2-natural transformations of the identity 2-superfunctor. -/
abbrev EndId (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
    [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B] :=
  TwoNatTrans (TwoSuperfunctor.id R B) (TwoSuperfunctor.id R B)

/-- The identity oplax functor of the underlying bicategory. -/
abbrev idU (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
    [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B] :
    OplaxFunctor (Underlying2 R B) (Underlying2 R B) :=
  OplaxFunctor.id (Underlying2 R B)

/-- A 2-natural transformation `𝕀 ⇒ 𝕀` as an oplax transformation of the identity of the
underlying bicategory. -/
def toOplax (θ : EndId R B) : idU R B ⟶ idU R B where
  app a := ⟨θ.X a.obj⟩
  naturality f := ⟨θ.x f.obj, θ.x_mem f.obj⟩
  naturality_naturality η := Subtype.ext (θ.naturality η.1)
  naturality_id a := Subtype.ext (by
    have h := θ.x_id a.obj
    simp only [TwoSuperfunctor.id_mapId, Iso.refl_hom, id_whiskerRight (R := R),
      whiskerLeft_id (R := R), Category.id_comp] at h
    change θ.x (𝟙 a.obj) ≫ θ.X a.obj ◁ 𝟙 (𝟙 a.obj) =
      𝟙 (𝟙 a.obj) ▷ θ.X a.obj ≫ (leftUnitor (θ.X a.obj)).hom ≫ (rightUnitor (θ.X a.obj)).inv
    rw [whiskerLeft_id (R := R), id_whiskerRight (R := R), Category.id_comp, Category.comp_id]
    have h' := congrArg
      (fun t => (leftUnitor (θ.X a.obj)).hom ≫ (rightUnitor (θ.X a.obj)).inv ≫ t) h
    simpa using h')
  naturality_comp f g := Subtype.ext (by
    have h := θ.x_comp f.obj g.obj
    simp only [TwoSuperfunctor.id_mapComp, Iso.refl_hom, id_whiskerRight (R := R),
      whiskerLeft_id (R := R), Category.id_comp, Category.comp_id] at h
    change θ.x (f.obj ≫ g.obj) ≫ θ.X _ ◁ 𝟙 (f.obj ≫ g.obj) =
      𝟙 (f.obj ≫ g.obj) ▷ θ.X _ ≫ (associator f.obj g.obj (θ.X _)).hom ≫ f.obj ◁ θ.x g.obj ≫
        (associator f.obj (θ.X _) g.obj).inv ≫ θ.x f.obj ▷ g.obj ≫
          (associator (θ.X _) f.obj g.obj).hom
    rw [whiskerLeft_id (R := R), id_whiskerRight (R := R), Category.id_comp,
      Category.comp_id, h])

/-- An oplax transformation of the identity of the underlying bicategory which is natural with
respect to all (not necessarily even) 2-morphisms, as a 2-natural transformation `𝕀 ⇒ 𝕀`. -/
def ofOplax (η : idU R B ⟶ idU R B)
    (nat : ∀ {a b : B} {f g : a ⟶ b} (ε : f ⟶ g),
      ε ▷ (η.app ⟨b⟩).obj ≫ (η.naturality (Underlying2.hom1 g)).1 =
        (η.naturality (Underlying2.hom1 f)).1 ≫ (η.app ⟨a⟩).obj ◁ ε) : EndId R B where
  X a := (η.app ⟨a⟩).obj
  x f := (η.naturality (Underlying2.hom1 f)).1
  x_mem f := (η.naturality (Underlying2.hom1 f)).2
  naturality ε := nat ε
  x_comp {a b c} f g := by
    have h := congrArg Subtype.val
      (η.naturality_comp (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) (Underlying2.hom1 f)
        (Underlying2.hom1 g))
    simp only [OplaxFunctor.id_mapComp, Underlying2.comp₂_val, Underlying2.whiskerLeft_val,
      Underlying2.whiskerRight_val, Underlying2.id₂_val, Underlying2.associator_hom_val,
      Underlying2.associator_inv_val, OplaxFunctor.id_toPrelaxFunctor, PrelaxFunctor.id_toPrelaxFunctorStruct,
      PrelaxFunctorStruct.id_toPrefunctor, Prefunctor.id_map, Underlying2.comp_obj,
      Underlying2.hom1_obj] at h
    simp only [TwoSuperfunctor.id_mapComp, TwoSuperfunctor.id_map, Iso.refl_hom]
    rw [whiskerLeft_id (R := R), id_whiskerRight (R := R), Category.id_comp,
      Category.comp_id] at h
    rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp, Category.comp_id]
    exact h
  x_id a := by
    have h := congrArg Subtype.val (η.naturality_id (⟨a⟩ : Underlying2 R B))
    simp only [OplaxFunctor.id_mapId, Underlying2.comp₂_val, Underlying2.whiskerLeft_val,
      Underlying2.whiskerRight_val, Underlying2.id₂_val, Underlying2.leftUnitor_hom_val,
      Underlying2.rightUnitor_inv_val, Underlying2.id_obj] at h
    simp only [TwoSuperfunctor.id_mapId, TwoSuperfunctor.id_obj, Iso.refl_hom]
    erw [whiskerLeft_id (R := R), Category.comp_id, id_whiskerRight (R := R),
      Category.id_comp] at h
    erw [id_whiskerRight (R := R), Category.id_comp, whiskerLeft_id (R := R)]
    change _ ≫ _ ≫ (η.naturality (𝟙 (⟨a⟩ : Underlying2 R B))).1 = _
    rw [h]
    simp

@[simp] theorem ofOplax_X (η : idU R B ⟶ idU R B) (nat) (a : B) :
    (ofOplax η nat).X a = (η.app ⟨a⟩).obj := rfl

@[simp] theorem ofOplax_x (η : idU R B ⟶ idU R B) (nat) {a b : B}
    (f : a ⟶ b) : (ofOplax η nat).x f = (η.naturality (Underlying2.hom1 f)).1 := rfl

@[simp] theorem toOplax_app (θ : EndId R B) (a : Underlying2 R B) :
    (toOplax θ).app a = ⟨θ.X a.obj⟩ := rfl

@[simp] theorem toOplax_naturality (θ : EndId R B) {a b : Underlying2 R B} (f : a ⟶ b) :
    ((toOplax θ).naturality f).1 = θ.x f.obj := rfl

/-- A modification of the associated oplax transformations (whose components are even) as a
supermodification. -/
@[simps]
def homOfModification {θ θ' : EndId R B} (Γ : Oplax.Modification θ.toOplax θ'.toOplax) :
    θ ⟶ θ' where
  app a := (Γ.app ⟨a⟩).1
  naturality f := (congrArg Subtype.val (Γ.naturality (Underlying2.hom1 f))).symm

/-- An isomorphism of the associated oplax transformations as an (even) isomorphism of
2-natural transformations. -/
@[simps]
def isoOfModificationIso {θ θ' : EndId R B} (e : θ.toOplax ≅ θ'.toOplax) : θ ≅ θ' where
  hom := homOfModification e.hom
  inv := homOfModification e.inv
  hom_inv_id := hom_ext fun a =>
    congrArg (fun Γ => Subtype.val (Oplax.Modification.app Γ ⟨a⟩)) e.hom_inv_id
  inv_hom_id := hom_ext fun a =>
    congrArg (fun Γ => Subtype.val (Oplax.Modification.app Γ ⟨a⟩)) e.inv_hom_id

end TwoNatTrans

/-! ## The Drinfeld center -/

variable (R B) in
/-- The Drinfeld center of a 2-supercategory (Brundan–Ellis, Definition 2.3): its objects are
the strong 2-natural transformations `𝕀 ⇒ 𝕀`, and its morphisms are the supermodifications. -/
structure DrinfeldCenter where
  /-- The underlying 2-natural transformation `(X, x) : 𝕀 ⇒ 𝕀`. -/
  toTwoNatTrans : TwoNatTrans.EndId R B
  isStrong : toTwoNatTrans.IsStrong

namespace DrinfeldCenter

open TwoNatTrans

instance : Category (DrinfeldCenter R B) where
  Hom X Y := X.toTwoNatTrans ⟶ Y.toTwoNatTrans
  id X := 𝟙 X.toTwoNatTrans
  comp f g := f ≫ g
  id_comp _ := TwoNatTrans.hom_ext fun _ => Category.id_comp _
  comp_id _ := TwoNatTrans.hom_ext fun _ => Category.comp_id _
  assoc _ _ _ := TwoNatTrans.hom_ext fun _ => Category.assoc _ _ _

instance (X Y : DrinfeldCenter R B) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (X.toTwoNatTrans ⟶ Y.toTwoNatTrans))

instance (X Y : DrinfeldCenter R B) : Module R (X ⟶ Y) :=
  inferInstanceAs (Module R (X.toTwoNatTrans ⟶ Y.toTwoNatTrans))

instance : Preadditive (DrinfeldCenter R B) where
  homGroup _ _ := inferInstance
  add_comp _ _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => Preadditive.comp_add _ _ _ _ _ _

instance : Linear R (DrinfeldCenter R B) where
  homModule _ _ := inferInstance
  smul_comp _ _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => Linear.comp_smul _ _ _ _ _ _

instance : Supercategory R (DrinfeldCenter R B) where
  parity X Y := parity (R := R) X.toTwoNatTrans Y.toTwoNatTrans
  isInternal X Y := isInternal (R := R) X.toTwoNatTrans Y.toTwoNatTrans
  id_mem X := id_mem (R := R) X.toTwoNatTrans
  comp_mem hf hg a := comp_mem (hf a) (hg a)

variable {X Y Z X' Y' Z' : DrinfeldCenter R B}

@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : ∀ a, f.app a = g.app a) : f = g :=
  TwoNatTrans.hom_ext h

@[simp] theorem id_app (X : DrinfeldCenter R B) (a : B) :
    (𝟙 X : X ⟶ X).app a = 𝟙 (X.toTwoNatTrans.X a) := rfl

@[simp] theorem comp_app (f : X ⟶ Y) (g : Y ⟶ Z) (a : B) : (f ≫ g).app a = f.app a ≫ g.app a :=
  rfl

@[simp] theorem add_app (f g : X ⟶ Y) (a : B) : (f + g).app a = f.app a + g.app a := rfl

@[simp] theorem smul_app (r : R) (f : X ⟶ Y) (a : B) : (r • f).app a = r • f.app a := rfl

theorem mem_parity_iff {p : ZMod 2} {f : X ⟶ Y} :
    f ∈ parity (R := R) X Y p ↔
      ∀ a, f.app a ∈ parity (R := R) (X.toTwoNatTrans.X a) (Y.toTwoNatTrans.X a) p := Iff.rfl

/-! ### The tensor product -/

/-- The tensor product `(X ⊗ Y)_λ := X_λ Y_λ`, `(x ⊗ y)_F := x_F y_F`. -/
def tensorObj (X Y : DrinfeldCenter R B) : DrinfeldCenter R B where
  toTwoNatTrans := ofOplax (Y.toTwoNatTrans.toOplax ≫ X.toTwoNatTrans.toOplax) (by
    intro a b f g ε
    change ε ▷ (Y.toTwoNatTrans.X b ≫ X.toTwoNatTrans.X b) ≫
        (associator g (Y.toTwoNatTrans.X b) (X.toTwoNatTrans.X b)).inv ≫
          Y.toTwoNatTrans.x g ▷ X.toTwoNatTrans.X b ≫
            (associator (Y.toTwoNatTrans.X a) g (X.toTwoNatTrans.X b)).hom ≫
              Y.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x g ≫
                (associator (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a) g).inv =
      ((associator f (Y.toTwoNatTrans.X b) (X.toTwoNatTrans.X b)).inv ≫
          Y.toTwoNatTrans.x f ▷ X.toTwoNatTrans.X b ≫
            (associator (Y.toTwoNatTrans.X a) f (X.toTwoNatTrans.X b)).hom ≫
              Y.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x f ≫
                (associator (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a) f).inv) ≫
        (Y.toTwoNatTrans.X a ≫ X.toTwoNatTrans.X a) ◁ ε
    have hY := Y.toTwoNatTrans.naturality ε
    have hX := X.toTwoNatTrans.naturality ε
    simp only [TwoSuperfunctor.id_map₂, TwoSuperfunctor.id_obj] at hX hY
    rw [associator_inv_naturality_left_assoc R, ← comp_whiskerRight'_assoc R, hY,
      comp_whiskerRight'_assoc R, associator_naturality_middle_assoc R,
      ← whiskerLeft_comp'_assoc R, hX, whiskerLeft_comp'_assoc R,
      associator_inv_naturality_right R]
    simp only [Category.assoc])
  isStrong {a b} f := by
    have := X.isStrong f
    have := Y.isStrong f
    have h1 : IsIso (Y.toTwoNatTrans.x f ▷ X.toTwoNatTrans.X b) :=
      (whiskerRightIso (R := R) (asIso (Y.toTwoNatTrans.x f)) (X.toTwoNatTrans.X b)).isIso_hom
    have h2 : IsIso (Y.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x f) :=
      (whiskerLeftIso (R := R) (Y.toTwoNatTrans.X a) (asIso (X.toTwoNatTrans.x f))).isIso_hom
    change IsIso ((associator f (Y.toTwoNatTrans.X b) (X.toTwoNatTrans.X b)).inv ≫
        Y.toTwoNatTrans.x f ▷ X.toTwoNatTrans.X b ≫
          (associator (Y.toTwoNatTrans.X a) f (X.toTwoNatTrans.X b)).hom ≫
            Y.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x f ≫
              (associator (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a) f).inv)
    infer_instance

@[simp] theorem tensorObj_X (X Y : DrinfeldCenter R B) (a : B) :
    (tensorObj X Y).toTwoNatTrans.X a = Y.toTwoNatTrans.X a ≫ X.toTwoNatTrans.X a := rfl

theorem tensorObj_x (X Y : DrinfeldCenter R B) {a b : B} (f : a ⟶ b) :
    (tensorObj X Y).toTwoNatTrans.x f =
      (associator f (Y.toTwoNatTrans.X b) (X.toTwoNatTrans.X b)).inv ≫
        Y.toTwoNatTrans.x f ▷ X.toTwoNatTrans.X b ≫
          (associator (Y.toTwoNatTrans.X a) f (X.toTwoNatTrans.X b)).hom ≫
            Y.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x f ≫
              (associator (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a) f).inv := rfl

variable (R B) in
/-- The unit object: `X_λ = 1_λ`, `x_F = λ_F⁻¹ ∘ ρ_F`. -/
def tensorUnit : DrinfeldCenter R B where
  toTwoNatTrans := ofOplax (𝟙 (idU R B)) (by
    intro a b f g ε
    change ε ▷ 𝟙 b ≫ (rightUnitor g).hom ≫ (leftUnitor g).inv =
      ((rightUnitor f).hom ≫ (leftUnitor f).inv) ≫ 𝟙 a ◁ ε
    rw [rightUnitor_naturality_assoc R, leftUnitor_inv_naturality R, Category.assoc])
  isStrong f := by
    change IsIso ((rightUnitor f).hom ≫ (leftUnitor f).inv)
    infer_instance

@[simp] theorem tensorUnit_X (a : B) : (tensorUnit R B).toTwoNatTrans.X a = 𝟙 a := rfl

theorem tensorUnit_x {a b : B} (f : a ⟶ b) :
    (tensorUnit R B).toTwoNatTrans.x f = (rightUnitor f).hom ≫ (leftUnitor f).inv := rfl

/-- `X ◁ β`: the component at `λ` is `β_λ ▷ X_λ` (the paper's `X_λ β_λ`). -/
def whiskerLeft (X : DrinfeldCenter R B) {Y Y' : DrinfeldCenter R B} (β : Y ⟶ Y') :
    tensorObj X Y ⟶ tensorObj X Y' where
  app a := β.app a ▷ X.toTwoNatTrans.X a
  naturality {a b} f := by
    change ((associator f (Y.toTwoNatTrans.X b) (X.toTwoNatTrans.X b)).inv ≫
        Y.toTwoNatTrans.x f ▷ X.toTwoNatTrans.X b ≫
          (associator (Y.toTwoNatTrans.X a) f (X.toTwoNatTrans.X b)).hom ≫
            Y.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x f ≫
              (associator (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a) f).inv) ≫
        (β.app a ▷ X.toTwoNatTrans.X a) ▷ f =
      f ◁ (β.app b ▷ X.toTwoNatTrans.X b) ≫
        (associator f (Y'.toTwoNatTrans.X b) (X.toTwoNatTrans.X b)).inv ≫
          Y'.toTwoNatTrans.x f ▷ X.toTwoNatTrans.X b ≫
            (associator (Y'.toTwoNatTrans.X a) f (X.toTwoNatTrans.X b)).hom ≫
              Y'.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x f ≫
                (associator (Y'.toTwoNatTrans.X a) (X.toTwoNatTrans.X a) f).inv
    have hβ := β.naturality f
    simp only [TwoSuperfunctor.id_map, TwoSuperfunctor.id_obj] at hβ
    simp only [Category.assoc]
    rw [← associator_inv_naturality_left R,
      ← whisker_exchange_of_even_right_assoc (β.app a) (X.toTwoNatTrans.x_mem f),
      ← associator_naturality_left_assoc R, ← comp_whiskerRight'_assoc R, hβ,
      comp_whiskerRight'_assoc R, ← associator_inv_naturality_middle_assoc R]

/-- `α ▷ Y`: the component at `λ` is `Y_λ ◁ α_λ` (the paper's `α_λ Y_λ`). -/
def whiskerRight {X X' : DrinfeldCenter R B} (α : X ⟶ X') (Y : DrinfeldCenter R B) :
    tensorObj X Y ⟶ tensorObj X' Y where
  app a := Y.toTwoNatTrans.X a ◁ α.app a
  naturality {a b} f := by
    change ((associator f (Y.toTwoNatTrans.X b) (X.toTwoNatTrans.X b)).inv ≫
        Y.toTwoNatTrans.x f ▷ X.toTwoNatTrans.X b ≫
          (associator (Y.toTwoNatTrans.X a) f (X.toTwoNatTrans.X b)).hom ≫
            Y.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x f ≫
              (associator (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a) f).inv) ≫
        (Y.toTwoNatTrans.X a ◁ α.app a) ▷ f =
      f ◁ (Y.toTwoNatTrans.X b ◁ α.app b) ≫
        (associator f (Y.toTwoNatTrans.X b) (X'.toTwoNatTrans.X b)).inv ≫
          Y.toTwoNatTrans.x f ▷ X'.toTwoNatTrans.X b ≫
            (associator (Y.toTwoNatTrans.X a) f (X'.toTwoNatTrans.X b)).hom ≫
              Y.toTwoNatTrans.X a ◁ X'.toTwoNatTrans.x f ≫
                (associator (Y.toTwoNatTrans.X a) (X'.toTwoNatTrans.X a) f).inv
    have hα := α.naturality f
    simp only [TwoSuperfunctor.id_map, TwoSuperfunctor.id_obj] at hα
    simp only [Category.assoc]
    rw [← associator_inv_naturality_middle R, ← whiskerLeft_comp'_assoc R, hα,
      whiskerLeft_comp'_assoc R, ← associator_naturality_right_assoc R,
      whisker_exchange_of_even_left_assoc (Y.toTwoNatTrans.x_mem f),
      ← associator_inv_naturality_right_assoc R]

@[simp] theorem whiskerLeft_app (X : DrinfeldCenter R B) {Y Y' : DrinfeldCenter R B}
    (β : Y ⟶ Y') (a : B) : (whiskerLeft X β).app a = β.app a ▷ X.toTwoNatTrans.X a := rfl

@[simp] theorem whiskerRight_app {X X' : DrinfeldCenter R B} (α : X ⟶ X')
    (Y : DrinfeldCenter R B) (a : B) :
    (whiskerRight α Y).app a = Y.toTwoNatTrans.X a ◁ α.app a := rfl

/-- An isomorphism of the underlying 2-natural transformations. -/
@[simps]
def isoMk {X Y : DrinfeldCenter R B} (e : X.toTwoNatTrans ≅ Y.toTwoNatTrans) : X ≅ Y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- The associator `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`, with components
`α⁻¹ : Z_λ ≫ Y_λ ≫ X_λ ≅ (Z_λ ≫ Y_λ) ≫ X_λ`. -/
def associator (X Y Z : DrinfeldCenter R B) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  isoMk <| isoOfModificationIso (θ := (tensorObj (tensorObj X Y) Z).toTwoNatTrans)
    (θ' := (tensorObj X (tensorObj Y Z)).toTwoNatTrans)
    (Bicategory.associator Z.toTwoNatTrans.toOplax Y.toTwoNatTrans.toOplax
      X.toTwoNatTrans.toOplax).symm

/-- The left unitor `1 ⊗ X ≅ X`, with components `ρ : X_λ ≫ 1_λ ≅ X_λ`. -/
def leftUnitor (X : DrinfeldCenter R B) : tensorObj (tensorUnit R B) X ≅ X :=
  isoMk <| isoOfModificationIso (θ := (tensorObj (tensorUnit R B) X).toTwoNatTrans)
    (θ' := X.toTwoNatTrans) (Bicategory.rightUnitor X.toTwoNatTrans.toOplax)

/-- The right unitor `X ⊗ 1 ≅ X`, with components `λ : 1_λ ≫ X_λ ≅ X_λ`. -/
def rightUnitor (X : DrinfeldCenter R B) : tensorObj X (tensorUnit R B) ≅ X :=
  isoMk <| isoOfModificationIso (θ := (tensorObj X (tensorUnit R B)).toTwoNatTrans)
    (θ' := X.toTwoNatTrans) (Bicategory.leftUnitor X.toTwoNatTrans.toOplax)

@[simp] theorem associator_hom_app (X Y Z : DrinfeldCenter R B) (a : B) :
    (associator X Y Z).hom.app a =
      (BicategoryStruct.associator (Z.toTwoNatTrans.X a) (Y.toTwoNatTrans.X a)
        (X.toTwoNatTrans.X a)).inv := rfl

@[simp] theorem associator_inv_app (X Y Z : DrinfeldCenter R B) (a : B) :
    (associator X Y Z).inv.app a =
      (BicategoryStruct.associator (Z.toTwoNatTrans.X a) (Y.toTwoNatTrans.X a)
        (X.toTwoNatTrans.X a)).hom := rfl

@[simp] theorem leftUnitor_hom_app (X : DrinfeldCenter R B) (a : B) :
    (leftUnitor X).hom.app a = (BicategoryStruct.rightUnitor (X.toTwoNatTrans.X a)).hom := rfl

@[simp] theorem leftUnitor_inv_app (X : DrinfeldCenter R B) (a : B) :
    (leftUnitor X).inv.app a = (BicategoryStruct.rightUnitor (X.toTwoNatTrans.X a)).inv := rfl

@[simp] theorem rightUnitor_hom_app (X : DrinfeldCenter R B) (a : B) :
    (rightUnitor X).hom.app a = (BicategoryStruct.leftUnitor (X.toTwoNatTrans.X a)).hom := rfl

@[simp] theorem rightUnitor_inv_app (X : DrinfeldCenter R B) (a : B) :
    (rightUnitor X).inv.app a = (BicategoryStruct.leftUnitor (X.toTwoNatTrans.X a)).inv := rfl

/-! ### The monoidal supercategory structure -/

instance : MonoidalCategoryStruct (DrinfeldCenter R B) where
  tensorObj := tensorObj
  whiskerLeft X _ _ β := whiskerLeft X β
  whiskerRight α Y := whiskerRight α Y
  tensorUnit := tensorUnit R B
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

section Simp

open MonoidalCategory

@[simp] theorem tensor_X (X Y : DrinfeldCenter R B) (a : B) :
    (X ⊗ Y).toTwoNatTrans.X a = Y.toTwoNatTrans.X a ≫ X.toTwoNatTrans.X a := rfl

@[simp] theorem unit_X (a : B) : (𝟙_ (DrinfeldCenter R B)).toTwoNatTrans.X a = 𝟙 a := rfl

@[simp] theorem mwhiskerLeft_app (X : DrinfeldCenter R B) {Y Y' : DrinfeldCenter R B}
    (β : Y ⟶ Y') (a : B) :
    (MonoidalCategoryStruct.whiskerLeft X β).app a = β.app a ▷ X.toTwoNatTrans.X a := rfl

@[simp] theorem mwhiskerRight_app {X X' : DrinfeldCenter R B} (α : X ⟶ X')
    (Y : DrinfeldCenter R B) (a : B) :
    (MonoidalCategoryStruct.whiskerRight α Y).app a = Y.toTwoNatTrans.X a ◁ α.app a := rfl

@[simp] theorem tensorHom_app {X₁ Y₁ X₂ Y₂ : DrinfeldCenter R B} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (a : B) : (f ⊗ g).app a =
      X₂.toTwoNatTrans.X a ◁ f.app a ≫ g.app a ▷ Y₁.toTwoNatTrans.X a := rfl

@[simp] theorem massociator_hom_app (X Y Z : DrinfeldCenter R B) (a : B) :
    (α_ X Y Z).hom.app a =
      (BicategoryStruct.associator (Z.toTwoNatTrans.X a) (Y.toTwoNatTrans.X a)
        (X.toTwoNatTrans.X a)).inv := rfl

@[simp] theorem massociator_inv_app (X Y Z : DrinfeldCenter R B) (a : B) :
    (α_ X Y Z).inv.app a =
      (BicategoryStruct.associator (Z.toTwoNatTrans.X a) (Y.toTwoNatTrans.X a)
        (X.toTwoNatTrans.X a)).hom := rfl

@[simp] theorem mleftUnitor_hom_app (X : DrinfeldCenter R B) (a : B) :
    (λ_ X).hom.app a = (BicategoryStruct.rightUnitor (X.toTwoNatTrans.X a)).hom := rfl

@[simp] theorem mrightUnitor_hom_app (X : DrinfeldCenter R B) (a : B) :
    (ρ_ X).hom.app a = (BicategoryStruct.leftUnitor (X.toTwoNatTrans.X a)).hom := rfl

@[simp] theorem zsmul_app (n : ℤ) (f : X ⟶ Y) (a : B) : (n • f).app a = n • f.app a := rfl

end Simp

/-- **Brundan–Ellis, Definition 2.3.** The Drinfeld center of a 2-supercategory is a monoidal
supercategory. -/
instance : MonoidalSupercategory R (DrinfeldCenter R B) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id X Y := hom_ext fun a => id_whiskerRight (R := R) _ _
  id_whiskerRight X Y := hom_ext fun a => whiskerLeft_id (R := R) _ _
  whiskerLeft_comp X _ _ _ f g := hom_ext fun a => comp_whiskerRight (R := R) _ _ _
  comp_whiskerRight f g W := hom_ext fun a => whiskerLeft_comp (R := R) _ _ _
  whiskerLeft_add X _ _ f g := hom_ext fun a => add_whiskerRight (R := R) _ _ _
  add_whiskerRight f g Z := hom_ext fun a => whiskerLeft_add (R := R) _ _ _
  whiskerLeft_smul X _ _ r f := hom_ext fun a => smul_whiskerRight (R := R) r _ _
  smul_whiskerRight r f Z := hom_ext fun a => whiskerLeft_smul (R := R) _ r _
  whiskerLeft_mem X _ _ _ _ hf a := TwoSupercategory.whiskerRight_mem _ (hf a)
  whiskerRight_mem Z hf a := TwoSupercategory.whiskerLeft_mem _ (hf a)
  super_interchange {X X' Y Y' p q f g} hf hg := hom_ext fun a => by
    change Y.toTwoNatTrans.X a ◁ f.app a ≫ g.app a ▷ X'.toTwoNatTrans.X a =
      koszulSign p q • (g.app a ▷ X.toTwoNatTrans.X a ≫ Y'.toTwoNatTrans.X a ◁ f.app a)
    rw [TwoSupercategory.super_interchange (hg a) (hf a), smul_smul, koszulSign_comm p q,
      koszulSign_mul_self, one_smul]
  associator_naturality f₁ f₂ f₃ := hom_ext fun a => by
    simp only [comp_app, tensorHom_app, massociator_hom_app, tensor_X, whiskerLeft_comp' R,
      comp_whiskerRight' R, Category.assoc, associator_inv_naturality_left R,
      associator_inv_naturality_middle_assoc R, associator_inv_naturality_right_assoc R]
  leftUnitor_naturality f := hom_ext fun a => by
    simp only [comp_app, mwhiskerLeft_app, mleftUnitor_hom_app, unit_X]
    exact rightUnitor_naturality R _
  rightUnitor_naturality f := hom_ext fun a => by
    simp only [comp_app, mwhiskerRight_app, mrightUnitor_hom_app, unit_X]
    exact leftUnitor_naturality R _
  pentagon W X Y Z := hom_ext fun a => by
    simp only [comp_app, mwhiskerLeft_app, mwhiskerRight_app, massociator_hom_app, tensor_X]
    exact pentagon_inv R _ _ _ _
  triangle X Y := hom_ext fun a => by
    simp only [comp_app, mwhiskerLeft_app, mwhiskerRight_app, massociator_hom_app,
      mleftUnitor_hom_app, mrightUnitor_hom_app, tensor_X, unit_X]
    rw [← TwoSupercategory.triangle (R := R), Iso.inv_hom_id_assoc]
  associator_hom_mem X Y Z a := inv_mem _ (associator_hom_mem (R := R) _ _ _)
  leftUnitor_hom_mem X a := rightUnitor_hom_mem (R := R) _
  rightUnitor_hom_mem X a := leftUnitor_hom_mem (R := R) _

end DrinfeldCenter

/-! ## Lemma 3.2: `(π, β)` in the Drinfeld center -/

namespace PiTwoSupercategory

open DrinfeldCenter MonoidalCategory

variable [PiTwoSupercategory R B]

variable (R B) in
/-- **Lemma 3.2 (i), (ii).** `(π, β)` is an object of the Drinfeld center: `X_λ := π_λ` and
`x_F := β_F`. -/
def centerObj : DrinfeldCenter R B where
  toTwoNatTrans :=
    { X := pi (R := R)
      x f := (β (R := R) f).hom
      x_mem f := β_hom_mem f
      naturality η := (β_naturality η).symm
      x_comp f g := by
        simp only [TwoSuperfunctor.id_mapComp, Iso.refl_hom, TwoSuperfunctor.id_map]
        erw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp,
          Category.comp_id]
        exact β_comp f g
      x_id a := by
        simp only [TwoSuperfunctor.id_mapId, Iso.refl_hom, TwoSuperfunctor.id_obj]
        erw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp]
        rw [β_id]
        simp }
  isStrong f := inferInstanceAs (IsIso (β (R := R) f).hom)

@[simp] theorem centerObj_X (a : B) : (centerObj R B).toTwoNatTrans.X a = pi (R := R) a := rfl

@[simp] theorem centerObj_x {a b : B} (f : a ⟶ b) :
    (centerObj R B).toTwoNatTrans.x f = (β (R := R) f).hom := rfl

variable (R B) in
/-- `ζ` is an odd isomorphism `(π, β) ≅ 1` in the Drinfeld center: the condition for a
supermodification is `β_hom_comp_ζ`. -/
def centerζ : centerObj R B ≅ 𝟙_ (DrinfeldCenter R B) where
  hom :=
    { app a := (ζ (R := R) a).hom
      naturality f := by
        change (β (R := R) f).hom ≫ (ζ (R := R) _).hom ▷ f =
          f ◁ (ζ (R := R) _).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv
        exact β_hom_comp_ζ f }
  inv :=
    { app a := (ζ (R := R) a).inv
      naturality f := by
        change ((rightUnitor f).hom ≫ (leftUnitor f).inv) ≫ (ζ (R := R) _).inv ▷ f =
          f ◁ (ζ (R := R) _).inv ≫ (β (R := R) f).hom
        rw [β_hom, TwoSupercategory.whiskerLeft_inv_hom_assoc R, Category.assoc] }
  hom_inv_id := hom_ext fun a => (ζ (R := R) a).hom_inv_id
  inv_hom_id := hom_ext fun a => (ζ (R := R) a).inv_hom_id

theorem centerζ_hom_mem :
    (centerζ R B).hom ∈ parity (R := R) (centerObj R B) (𝟙_ (DrinfeldCenter R B)) 1 :=
  fun a => ζ_hom_mem (R := R) a

variable (R B) in
/-- **Lemma 3.2(iv).** `ξ = ζζ` is an even isomorphism `(π, β) ⊗ (π, β) ≅ 1` in the Drinfeld
center; the condition for a supermodification is the identity of Lemma 3.2(iv)
(`ξ_comm`). -/
def centerξ : centerObj R B ⊗ centerObj R B ≅ 𝟙_ (DrinfeldCenter R B) where
  hom :=
    { app a := (ξ (R := R) a).hom
      naturality {a b} f := by
        change ((associator f (pi (R := R) b) (pi (R := R) b)).inv ≫
            (β (R := R) f).hom ▷ pi (R := R) b ≫
              (associator (pi (R := R) a) f (pi (R := R) b)).hom ≫
                pi (R := R) a ◁ (β (R := R) f).hom ≫
                  (associator (pi (R := R) a) (pi (R := R) a) f).inv) ≫
            (ξ (R := R) a).hom ▷ f =
          f ◁ (ξ (R := R) b).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv
        rw [← ξ_comm]
        simp only [Category.assoc, TwoSupercategory.inv_hom_whiskerRight R, Category.comp_id] }
  inv :=
    { app a := (ξ (R := R) a).inv
      naturality {a b} f := by
        change ((rightUnitor f).hom ≫ (leftUnitor f).inv) ≫ (ξ (R := R) a).inv ▷ f =
          f ◁ (ξ (R := R) b).inv ≫ ((associator f (pi (R := R) b) (pi (R := R) b)).inv ≫
            (β (R := R) f).hom ▷ pi (R := R) b ≫
              (associator (pi (R := R) a) f (pi (R := R) b)).hom ≫
                pi (R := R) a ◁ (β (R := R) f).hom ≫
                  (associator (pi (R := R) a) (pi (R := R) a) f).inv)
        rw [← ξ_comm]
        simp only [Category.assoc, TwoSupercategory.whiskerLeft_inv_hom_assoc R] }
  hom_inv_id := hom_ext fun a => (ξ (R := R) a).hom_inv_id
  inv_hom_id := hom_ext fun a => (ξ (R := R) a).inv_hom_id

theorem centerξ_hom_mem :
    (centerξ R B).hom ∈
      parity (R := R) (centerObj R B ⊗ centerObj R B) (𝟙_ (DrinfeldCenter R B)) 0 :=
  fun a => ξ_hom_mem (R := R) a

/-- `ξ = ζζ` in the Drinfeld center: the component of `centerξ` is the tensor product (in the
sense of the paper, `MonoidalSupercategory.superTensorHom`) of `ζ` with itself, followed by
the unitor. -/
theorem centerξ_hom_eq :
    (centerξ R B).hom = MonoidalSupercategory.superTensorHom (centerζ R B).hom (centerζ R B).hom ≫
      (λ_ (𝟙_ (DrinfeldCenter R B))).hom :=
  hom_ext fun a => by
    change (ξ (R := R) a).hom = ((ζ (R := R) a).hom ▷ pi (R := R) a ≫
      𝟙 a ◁ (ζ (R := R) a).hom) ≫ (BicategoryStruct.rightUnitor (𝟙 a)).hom
    rw [ξ_hom_eq_hcomp, hcomp, unitors_equal R, Category.assoc]

end PiTwoSupercategory

end StringDiagrams

end
