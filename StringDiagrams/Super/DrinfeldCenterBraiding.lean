import StringDiagrams.Super.DrinfeldCenter
import StringDiagrams.Super.Braided

/-!
# The braiding of the Drinfeld center

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, remark after
Definition 2.3: "the Drinfeld center of a 2-supercategory is a braided monoidal supercategory,
although we omit the definition of such a structure". This module goes beyond the text of the
paper: with the notion of braided monoidal supercategory of `StringDiagrams.Super.Braided`, the
Drinfeld center `Z(𝔄)` of a 2-supercategory is braided by the standard braiding given by the
half-braidings, `c_{(X,x),(Y,y)} := (x_{Y_λ})_λ : X_λ Y_λ ⇒ Y_λ X_λ` (in the diagrammatic order,
`x_{Y_λ} : Y_λ ≫ X_λ ⟶ X_λ ≫ Y_λ`), instance `DrinfeldCenter.instBraidedMonoidalSupercategory`.
The supermodification condition for `c` is the naturality of `x` with respect to the
2-morphisms `y_F` together with the coherence axiom of Definition 2.2(iii)
(`DrinfeldCenter.braidingApp_naturality`); naturality of `c` in `(X, x)` is the
supermodification condition, naturality in `(Y, y)` is the naturality of `x` with respect to
2-morphisms, and the two hexagon axioms are the coherence axiom of Definition 2.2(iii) for
`x` and for `x ⊗ y`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory MonoidalCategory

universe w v u w₁

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

namespace TwoNatTrans

/-- The coherence axiom of Definition 2.2(iii) for a 2-natural transformation `𝕀 ⇒ 𝕀`, solved
for `x_{GF}`: `x_{f ≫ g} = α ∘ (f ◁ x_g) ∘ α⁻¹ ∘ (x_f ▷ g) ∘ α`. -/
theorem EndId.x_comp' (θ : EndId R B) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    θ.x (f ≫ g) = (BicategoryStruct.associator f g (θ.X c)).hom ≫ f ◁ θ.x g ≫
      (BicategoryStruct.associator f (θ.X b) g).inv ≫ θ.x f ▷ g ≫ (BicategoryStruct.associator (θ.X a) f g).hom := by
  have h := θ.x_comp f g
  simp only [TwoSuperfunctor.id_mapComp, Iso.refl_hom, TwoSuperfunctor.id_map] at h
  erw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp,
    Category.comp_id] at h
  exact h

end TwoNatTrans

namespace DrinfeldCenter

variable (X Y : DrinfeldCenter R B)

/-- The component `x_{Y_λ} : Y_λ ≫ X_λ ⟶ X_λ ≫ Y_λ` of the braiding. -/
abbrev braidingApp (a : B) : (X ⊗ Y).toTwoNatTrans.X a ⟶ (Y ⊗ X).toTwoNatTrans.X a :=
  X.toTwoNatTrans.x (Y.toTwoNatTrans.X a)

/-- The supermodification condition for the braiding. -/
theorem braidingApp_naturality {a b : B} (f : a ⟶ b) :
    (X ⊗ Y).toTwoNatTrans.x f ≫ braidingApp X Y a ▷ (TwoSuperfunctor.id R B).map f =
      (TwoSuperfunctor.id R B).map f ◁ braidingApp X Y b ≫ (Y ⊗ X).toTwoNatTrans.x f := by
  have h := X.toTwoNatTrans.naturality (Y.toTwoNatTrans.x f)
  simp only [TwoSuperfunctor.id_map₂, TwoSuperfunctor.id_map] at h
  rw [TwoNatTrans.EndId.x_comp', TwoNatTrans.EndId.x_comp'] at h
  change ((BicategoryStruct.associator f (Y.toTwoNatTrans.X b) (X.toTwoNatTrans.X b)).inv ≫
      Y.toTwoNatTrans.x f ▷ X.toTwoNatTrans.X b ≫
        (BicategoryStruct.associator (Y.toTwoNatTrans.X a) f (X.toTwoNatTrans.X b)).hom ≫
          Y.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x f ≫
            (BicategoryStruct.associator (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a) f).inv) ≫
              X.toTwoNatTrans.x (Y.toTwoNatTrans.X a) ▷ f =
    f ◁ X.toTwoNatTrans.x (Y.toTwoNatTrans.X b) ≫
      ((BicategoryStruct.associator f (X.toTwoNatTrans.X b) (Y.toTwoNatTrans.X b)).inv ≫
        X.toTwoNatTrans.x f ▷ Y.toTwoNatTrans.X b ≫
          (BicategoryStruct.associator (X.toTwoNatTrans.X a) f (Y.toTwoNatTrans.X b)).hom ≫
            X.toTwoNatTrans.X a ◁ Y.toTwoNatTrans.x f ≫
              (BicategoryStruct.associator (X.toTwoNatTrans.X a) (Y.toTwoNatTrans.X a) f).inv)
  simp only [Category.assoc]
  rw [← cancel_mono (BicategoryStruct.associator (X.toTwoNatTrans.X a) (Y.toTwoNatTrans.X a) f).hom,
    ← cancel_epi (BicategoryStruct.associator f (Y.toTwoNatTrans.X b) (X.toTwoNatTrans.X b)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using h

/-- The braiding `c_{(X,x),(Y,y)} : (X, x) ⊗ (Y, y) ≅ (Y, y) ⊗ (X, x)` of the Drinfeld center,
with components `x_{Y_λ}`. -/
def braiding : X ⊗ Y ≅ Y ⊗ X where
  hom := ⟨braidingApp X Y, braidingApp_naturality X Y⟩
  inv :=
    { app := fun a => by
        haveI := X.isStrong (Y.toTwoNatTrans.X a)
        exact inv (braidingApp X Y a)
      naturality := fun {a b} f => by
        haveI := X.isStrong (Y.toTwoNatTrans.X a)
        haveI := X.isStrong (Y.toTwoNatTrans.X b)
        have h := congrArg (fun t => (TwoSuperfunctor.id R B).map f ◁ inv (braidingApp X Y b) ≫
          t ≫ inv (braidingApp X Y a) ▷ (TwoSuperfunctor.id R B).map f)
          (braidingApp_naturality X Y f)
        simp only [Category.assoc] at h
        rw [← comp_whiskerRight (R := R), IsIso.hom_inv_id, id_whiskerRight (R := R),
          Category.comp_id, ← whiskerLeft_comp'_assoc R, IsIso.inv_hom_id,
          whiskerLeft_id (R := R), Category.id_comp] at h
        exact h.symm }
  hom_inv_id := TwoNatTrans.hom_ext fun a => by
    haveI := X.isStrong (Y.toTwoNatTrans.X a)
    exact IsIso.hom_inv_id _
  inv_hom_id := TwoNatTrans.hom_ext fun a => by
    haveI := X.isStrong (Y.toTwoNatTrans.X a)
    exact IsIso.inv_hom_id _

@[simp] theorem braiding_hom_app (a : B) :
    (braiding X Y).hom.app a = X.toTwoNatTrans.x (Y.toTwoNatTrans.X a) := rfl

/-- **The Drinfeld center is braided** (extension beyond Brundan–Ellis, who omit the
definition): the braiding is given by the half-braidings, `c_{(X,x),(Y,y)} = x_{Y_λ}`. -/
instance instBraidedMonoidalSupercategory : BraidedMonoidalSupercategory R (DrinfeldCenter R B) where
  braiding := braiding
  braiding_hom_mem X Y a := X.toTwoNatTrans.x_mem _
  braiding_naturality_right X _ _ β := TwoNatTrans.hom_ext fun a => by
    simp only [comp_app, mwhiskerLeft_app, mwhiskerRight_app, braiding_hom_app]
    have h := X.toTwoNatTrans.naturality (β.app a)
    simpa only [TwoSuperfunctor.id_map₂, TwoSuperfunctor.id_map] using h
  braiding_naturality_left α Z := TwoNatTrans.hom_ext fun a => by
    simp only [comp_app, mwhiskerLeft_app, mwhiskerRight_app, braiding_hom_app]
    have h := α.naturality (Z.toTwoNatTrans.X a)
    simpa only [TwoSuperfunctor.id_map] using h.symm
  hexagon_forward X Y Z := TwoNatTrans.hom_ext fun a => by
    simp only [comp_app, mwhiskerLeft_app, mwhiskerRight_app, braiding_hom_app,
      massociator_hom_app, tensor_X]
    rw [TwoNatTrans.EndId.x_comp']
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  hexagon_reverse X Y Z := TwoNatTrans.hom_ext fun a => by
    simp only [comp_app, mwhiskerLeft_app, mwhiskerRight_app, braiding_hom_app,
      massociator_inv_app, tensor_X]
    change (BicategoryStruct.associator (Z.toTwoNatTrans.X a) (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a)).hom ≫
      ((BicategoryStruct.associator (Z.toTwoNatTrans.X a) (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a)).inv ≫
        Y.toTwoNatTrans.x (Z.toTwoNatTrans.X a) ▷ X.toTwoNatTrans.X a ≫
          (BicategoryStruct.associator (Y.toTwoNatTrans.X a) (Z.toTwoNatTrans.X a) (X.toTwoNatTrans.X a)).hom ≫
            Y.toTwoNatTrans.X a ◁ X.toTwoNatTrans.x (Z.toTwoNatTrans.X a) ≫
              (BicategoryStruct.associator (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a)
                (Z.toTwoNatTrans.X a)).inv) ≫
      (BicategoryStruct.associator (Y.toTwoNatTrans.X a) (X.toTwoNatTrans.X a) (Z.toTwoNatTrans.X a)).hom = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

end DrinfeldCenter

end StringDiagrams

end
