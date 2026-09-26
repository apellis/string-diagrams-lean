import StringDiagrams.Super.DrinfeldCenter
import StringDiagrams.Super.TwoEnvelopeFunctor
import StringDiagrams.Super.TwoEnvelopePi
import StringDiagrams.Super.MonoidalPi

/-!
# The Drinfeld center of the Π-envelope

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Remark 4.10 (last sentence) and Section 3.

* For a Π-2-supercategory `𝔅`, the Drinfeld center `Z(𝔅)` is a monoidal Π-supercategory in the
  sense of Definition 1.12, with `π = (π, β)` and `ζ` the odd isomorphism `(π, β) ≅ 1` of
  Lemma 3.2 (instance `DrinfeldCenter.instMonoidalPiSupercategory`).
* For a 2-supercategory `𝔄`, the strict 2-functor `-_π` of (4.7) (on the endomorphisms of `𝕀`,
  with `𝕀_π = 𝕀`) induces a monoidal superfunctor from the Drinfeld center of `𝔄` to the
  Drinfeld center of `𝔄_π`: `(X, x) ↦ (X_π, x_π)` with `(X_π)_λ = Π⁰X_λ`,
  `(x_π)_{ΠᵃF} = (x_F)_a^a`, and `α ↦ α_π`, `(α_π)_λ = (α_λ)_0^0`
  (`DrinfeldCenter.mapPi`, a superfunctor; `DrinfeldCenter.mapPiMonoidal`, its monoidal
  structure, with identity coherence maps: `Π⁰Y_λ ≫ Π⁰X_λ = Π⁰(Y_λ ≫ X_λ)` on the nose).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory MonoidalCategory

universe w v u w₁

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

namespace DrinfeldCenter

/-! ## The Drinfeld center of a Π-2-supercategory is a monoidal Π-supercategory -/

/-- **Brundan–Ellis, Lemma 3.2 and Remark 4.10.** The Drinfeld center of a Π-2-supercategory is
a monoidal Π-supercategory (Definition 1.12), with `π = (π, β)` and `ζ` the odd isomorphism
`(π, β) ≅ 1` of Lemma 3.2. -/
instance instMonoidalPiSupercategory [PiTwoSupercategory R B] :
    MonoidalPiSupercategory R (DrinfeldCenter R B) where
  pi := PiTwoSupercategory.centerObj R B
  ζ := PiTwoSupercategory.centerζ R B
  ζ_hom_mem := PiTwoSupercategory.centerζ_hom_mem

/-! ## The superfunctor `Z(𝔄) → Z(𝔄_π)` -/

open TwoEnvelope Envelope

omit [TwoSupercategory R B] in
theorem toHom_comp₂ {a b : TwoEnvelope R B} {f g h : a ⟶ b} (x : f ⟶ g) (y : g ⟶ h) :
    toHom (x ≫ y) = toHom x ≫ toHom y := rfl

omit [TwoSupercategory R B] in
theorem toHom_id₂ {a b : TwoEnvelope R B} (f : a ⟶ b) : toHom (𝟙 f) = 𝟙 f.obj := rfl

omit [TwoSupercategory R B] in
@[simp] theorem Jm_par {a b : B} (f : a ⟶ b) : (Jm (R := R) f).par = 0 := rfl

omit [TwoSupercategory R B] in
@[simp] theorem Jm_obj {a b : B} (f : a ⟶ b) : (Jm (R := R) f).obj = f := rfl

theorem tensor_x (X Y : DrinfeldCenter R B) {a b : B} (f : a ⟶ b) :
    (X ⊗ Y).toTwoNatTrans.x f =
      (BicategoryStruct.associator f (Y.toTwoNatTrans.X b) (X.toTwoNatTrans.X b)).inv ≫
        Y.toTwoNatTrans.x f ▷ X.toTwoNatTrans.X b ≫
          (BicategoryStruct.associator (Y.toTwoNatTrans.X a) f (X.toTwoNatTrans.X b)).hom ≫
            Y.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x f ≫
              (BicategoryStruct.associator (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a) f).inv :=
  rfl

theorem unit_x {a b : B} (f : a ⟶ b) :
    (𝟙_ (DrinfeldCenter R B)).toTwoNatTrans.x f =
      (BicategoryStruct.rightUnitor f).hom ≫ (BicategoryStruct.leftUnitor f).inv := rfl

/-- **Remark 4.10.** The object `(X_π, x_π)` of the Drinfeld center of `𝔄_π` induced by an object
`(X, x)` of the Drinfeld center of `𝔄`. -/
def mapPiObj (X : DrinfeldCenter R B) : DrinfeldCenter R (TwoEnvelope R B) where
  toTwoNatTrans := mapPiNatTrans X.toTwoNatTrans
  isStrong f := by
    haveI := X.isStrong f.obj
    exact ⟨⟨Envelope.ofHom (inv (X.toTwoNatTrans.x f.obj)),
      Envelope.hom_ext (by
        rw [Envelope.toHom_comp, Envelope.toHom_ofHom]
        erw [Envelope.toHom_ofHom, IsIso.hom_inv_id]
        rfl),
      Envelope.hom_ext (by
        rw [Envelope.toHom_comp, Envelope.toHom_ofHom]
        erw [Envelope.toHom_ofHom, IsIso.inv_hom_id]
        rfl)⟩⟩

@[simp] theorem mapPiObj_X (X : DrinfeldCenter R B) (a : TwoEnvelope R B) :
    (mapPiObj X).toTwoNatTrans.X a = Jm (X.toTwoNatTrans.X a.as) := rfl

theorem toHom_mapPiObj_x (X : DrinfeldCenter R B) {a b : TwoEnvelope R B} (f : a ⟶ b) :
    toHom ((mapPiObj X).toTwoNatTrans.x f :
      (TwoSuperfunctor.id R (TwoEnvelope R B)).map f ≫ Jm (X.toTwoNatTrans.X b.as) ⟶
        Jm (X.toTwoNatTrans.X a.as) ≫ (TwoSuperfunctor.id R (TwoEnvelope R B)).map f) =
      X.toTwoNatTrans.x f.obj := rfl

variable (R B) in
/-- **Remark 4.10.** The superfunctor `Z(𝔄) → Z(𝔄_π)`, `(X, x) ↦ (X_π, x_π)`, `α ↦ α_π`. -/
def mapPi : DrinfeldCenter R B ⥤ DrinfeldCenter R (TwoEnvelope R B) where
  obj := mapPiObj
  map α := mapPiSupermodification α
  map_id _ := TwoNatTrans.hom_ext fun _ => rfl
  map_comp _ _ := TwoNatTrans.hom_ext fun _ => rfl

@[simp] theorem mapPi_obj (X : DrinfeldCenter R B) : (mapPi R B).obj X = mapPiObj X := rfl

theorem mapPi_map_app {X Y : DrinfeldCenter R B} (α : X ⟶ Y) (a : TwoEnvelope R B) :
    ((mapPi R B).map α).app a = J2 (α.app a.as) := rfl

omit [TwoSupercategory R B] in
theorem toHom_J2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : toHom (J2 (R := R) η) = η := rfl

instance : (mapPi R B).Additive where
  map_add := TwoNatTrans.hom_ext fun _ => rfl

instance : (mapPi R B).Linear R where
  map_smul _ _ := TwoNatTrans.hom_ext fun _ => rfl

instance : IsSuperfunctor R (mapPi R B) where
  map_mem {X Y p α} hα a := by
    rw [mapPi_map_app, Envelope.mem_parity_iff, toHom_J2]
    simpa using hα a.as

/-! ## The monoidal structure -/

/-- The coherence isomorphism `X_π ⊗ Y_π ≅ (X ⊗ Y)_π`, with identity components
(`Π⁰Y_λ ≫ Π⁰X_λ = Π⁰(Y_λ ≫ X_λ)`). -/
def mapPiμ (X Y : DrinfeldCenter R B) : mapPiObj X ⊗ mapPiObj Y ≅ mapPiObj (X ⊗ Y) where
  hom :=
    { app := fun a => 𝟙 _
      naturality := fun {a b} f => by
        erw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.comp_id,
          Category.id_comp]
        apply Envelope.hom_ext
        erw [toHom_mapPiObj_x]
        rw [tensor_x, tensor_x]
        erw [toHom_comp₂, toHom_comp₂, toHom_comp₂, toHom_comp₂,
          TwoEnvelope.toHom_associator_inv, TwoEnvelope.toHom_associator_inv,
          TwoEnvelope.toHom_associator_hom, TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl,
          TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl, toHom_mapPiObj_x, toHom_mapPiObj_x]
        rfl }
  inv :=
    { app := fun a => 𝟙 _
      naturality := fun {a b} f => by
        erw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.comp_id,
          Category.id_comp]
        apply Envelope.hom_ext
        erw [toHom_mapPiObj_x]
        rw [tensor_x, tensor_x]
        erw [toHom_comp₂, toHom_comp₂, toHom_comp₂, toHom_comp₂,
          TwoEnvelope.toHom_associator_inv, TwoEnvelope.toHom_associator_inv,
          TwoEnvelope.toHom_associator_hom, TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl,
          TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl, toHom_mapPiObj_x, toHom_mapPiObj_x]
        rfl }
  hom_inv_id := TwoNatTrans.hom_ext fun _ => Category.id_comp _
  inv_hom_id := TwoNatTrans.hom_ext fun _ => Category.id_comp _

theorem mapPiμ_hom_app (X Y : DrinfeldCenter R B) (a : TwoEnvelope R B) :
    (mapPiμ X Y).hom.app a = 𝟙 _ := rfl

/-- The coherence isomorphism `1 ≅ 1_π`, with identity components. -/
def mapPiε : 𝟙_ (DrinfeldCenter R (TwoEnvelope R B)) ≅ mapPiObj (𝟙_ (DrinfeldCenter R B)) where
  hom :=
    { app := fun a => 𝟙 _
      naturality := fun {a b} f => by
        erw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.comp_id,
          Category.id_comp]
        apply Envelope.hom_ext
        erw [toHom_mapPiObj_x]
        rw [unit_x, unit_x]
        erw [toHom_comp₂, TwoEnvelope.toHom_rightUnitor_hom,
          TwoEnvelope.toHom_leftUnitor_inv] }
  inv :=
    { app := fun a => 𝟙 _
      naturality := fun {a b} f => by
        erw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.comp_id,
          Category.id_comp]
        apply Envelope.hom_ext
        erw [toHom_mapPiObj_x] }
  hom_inv_id := TwoNatTrans.hom_ext fun _ => Category.id_comp _
  inv_hom_id := TwoNatTrans.hom_ext fun _ => Category.id_comp _

theorem mapPiε_hom_app (a : TwoEnvelope R B) : (mapPiε (R := R) (B := B)).hom.app a = 𝟙 _ := rfl

variable (R B) in
/-- **Brundan–Ellis, Remark 4.10.** The strict 2-functor `-_π` induces a monoidal superfunctor
from the Drinfeld center of `𝔄` to the Drinfeld center of `𝔄_π`, with identity coherence maps. -/
def mapPiMonoidal : MonoidalSuperfunctor R (mapPi R B) where
  μIso := mapPiμ
  εIso := mapPiε
  μ_mem _ _ _ := id_mem _
  ε_mem _ := id_mem _
  μ_natural_left f X' := TwoNatTrans.hom_ext fun a => by
    simp only [comp_app, mwhiskerRight_app, mapPi_obj, mapPi_map_app, mapPiμ_hom_app,
      mapPiObj_X]
    erw [Category.comp_id, Category.id_comp]
    apply Envelope.hom_ext
    erw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
    rfl
  μ_natural_right X' f := TwoNatTrans.hom_ext fun a => by
    simp only [comp_app, mwhiskerLeft_app, mapPi_obj, mapPi_map_app, mapPiμ_hom_app,
      mapPiObj_X]
    erw [Category.comp_id, Category.id_comp]
    apply Envelope.hom_ext
    erw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
    rfl
  associativity X Y Z := TwoNatTrans.hom_ext fun a => by
    simp only [comp_app, mwhiskerRight_app, mwhiskerLeft_app, mapPi_obj, mapPi_map_app,
      mapPiμ_hom_app, mapPiObj_X, massociator_hom_app, tensor_X]
    erw [whiskerLeft_id (R := R), id_whiskerRight (R := R), Category.id_comp, Category.id_comp,
      Category.comp_id, Category.comp_id]
    apply Envelope.hom_ext
    erw [TwoEnvelope.toHom_associator_inv]
    rfl
  left_unitality X := TwoNatTrans.hom_ext fun a => by
    simp only [comp_app, mwhiskerRight_app, mapPi_obj, mapPi_map_app, mapPiμ_hom_app,
      mapPiε_hom_app, mapPiObj_X, mleftUnitor_hom_app, unit_X]
    erw [whiskerLeft_id (R := R), Category.id_comp, Category.id_comp]
    apply Envelope.hom_ext
    erw [TwoEnvelope.toHom_rightUnitor_hom]
  right_unitality X := TwoNatTrans.hom_ext fun a => by
    simp only [comp_app, mwhiskerLeft_app, mapPi_obj, mapPi_map_app, mapPiμ_hom_app,
      mapPiε_hom_app, mapPiObj_X, mrightUnitor_hom_app, unit_X]
    erw [id_whiskerRight (R := R), Category.id_comp, Category.id_comp]
    apply Envelope.hom_ext
    erw [TwoEnvelope.toHom_leftUnitor_hom]

end DrinfeldCenter

end StringDiagrams

end
