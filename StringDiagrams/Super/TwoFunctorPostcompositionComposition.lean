import StringDiagrams.Super.TwoFunctorPostcomposition

/-!
# The compositor of actual postcomposition

The comparison uses the compositor of the postcomposing functor, with no
strictness assumption. Its naturality is proved directly in the supercategory.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ w
variable {R : Type w} [CommRing R]
  {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A]
  {B : Type u₂} [BicategoryStruct.{w₂, v₂} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₃} [BicategoryStruct.{w₃, v₃} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
namespace TwoNatTrans
variable (H : TwoSuperfunctor R B C) {F G K : TwoSuperfunctor R A B}
  (θ : TwoNatTrans F G) (ψ : TwoNatTrans G K)

omit [TwoSupercategory R B] [TwoSupercategory R C] in
private theorem compositor_associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) :
    (BicategoryStruct.associator (H.map f) (H.map g) (H.map h)).hom ≫
      H.map f ◁ (H.mapComp g h).hom ≫ (H.mapComp f (g ≫ h)).hom =
    (H.mapComp f g).hom ▷ H.map h ≫ (H.mapComp (f ≫ g) h).hom ≫
      H.map₂ (BicategoryStruct.associator f g h).hom := by
  rw [← cancel_mono (H.map₂Iso (BicategoryStruct.associator f g h)).inv]
  simp only [Category.assoc, TwoSuperfunctor.map₂Iso_inv, ← H.map₂_comp,
    Iso.hom_inv_id, H.map₂_id, Category.comp_id]
  rw [H.map₂_associator, Iso.hom_inv_id_assoc]

/-- The actual compositor satisfies the modification square at every 1-cell. -/
theorem postcomposeVcomp_hom_naturality {a b : A} (f : a ⟶ b) :
    (vcomp (postcompose H θ) (postcompose H ψ)).x f ≫
        (H.mapComp (θ.X a) (ψ.X a)).hom ▷ H.map (K.map f) =
      H.map (F.map f) ◁ (H.mapComp (θ.X b) (ψ.X b)).hom ≫
        (postcompose H (vcomp θ ψ)).x f := by
  simp only [vcomp_x, postcompose_x, postcompose_X, vcomp_X,
    comp_whiskerRight (R := R), whiskerLeft_comp (R := R), H.map₂_comp, Category.assoc]
  dsimp only [TwoSuperfunctor.comp]
  rw [← cancel_mono (H.mapComp (θ.X a ≫ ψ.X a) (K.map f)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [H.map₂_associator_assoc]
  rw [← H.map₂_associator (θ.X a) (ψ.X a) (K.map f)]
  rw [whiskerLeft_inv_hom_assoc R, H.mapComp_naturality_right_assoc,
    reassoc_of% (compositor_associator H (θ.X a) (G.map f) (ψ.X b)),
    inv_hom_whiskerRight_assoc R, H.mapComp_naturality_left_assoc]

/-- The inverse compositor satisfies the opposite modification square. -/
theorem postcomposeVcomp_inv_naturality {a b : A} (f : a ⟶ b) :
    (postcompose H (vcomp θ ψ)).x f ≫
        (H.mapComp (θ.X a) (ψ.X a)).inv ▷ H.map (K.map f) =
      H.map (F.map f) ◁ (H.mapComp (θ.X b) (ψ.X b)).inv ≫
        (vcomp (postcompose H θ) (postcompose H ψ)).x f := by
  rw [← cancel_epi (whiskerLeftIso (R := R) (H.map (F.map f))
    (H.mapComp (θ.X b) (ψ.X b))).hom]
  change H.map (F.map f) ◁ (H.mapComp (θ.X b) (ψ.X b)).hom ≫ _ = _
  dsimp only [whiskerLeftIso]
  erw [← Category.assoc, ← postcomposeVcomp_hom_naturality H θ ψ f,
    Category.assoc, hom_inv_whiskerRight R, Category.comp_id,
    ← Category.assoc, whiskerLeft_hom_inv R, Category.id_comp]

/-- The genuine compositor of postcomposition, with its actual `mapComp` components. -/
def postcomposeVcompIso :
    vcomp (postcompose H θ) (postcompose H ψ) ≅ postcompose H (vcomp θ ψ) where
  hom := ⟨fun a => (H.mapComp (θ.X a) (ψ.X a)).hom,
    postcomposeVcomp_hom_naturality H θ ψ⟩
  inv := ⟨fun a => (H.mapComp (θ.X a) (ψ.X a)).inv,
    postcomposeVcomp_inv_naturality H θ ψ⟩
  hom_inv_id := hom_ext fun a => (H.mapComp (θ.X a) (ψ.X a)).hom_inv_id
  inv_hom_id := hom_ext fun a => (H.mapComp (θ.X a) (ψ.X a)).inv_hom_id

@[simp] theorem postcomposeVcompIso_hom_app (a : A) :
    (postcomposeVcompIso H θ ψ).hom.app a = (H.mapComp (θ.X a) (ψ.X a)).hom := rfl

@[simp] theorem postcomposeVcompIso_inv_app (a : A) :
    (postcomposeVcompIso H θ ψ).inv.app a = (H.mapComp (θ.X a) (ψ.X a)).inv := rfl

theorem postcomposeVcompIso_hom_inv_id :
    (postcomposeVcompIso H θ ψ).hom ≫ (postcomposeVcompIso H θ ψ).inv =
      𝟙 (vcomp (postcompose H θ) (postcompose H ψ)) :=
  (postcomposeVcompIso H θ ψ).hom_inv_id

theorem postcomposeVcompIso_inv_hom_id :
    (postcomposeVcompIso H θ ψ).inv ≫ (postcomposeVcompIso H θ ψ).hom =
      𝟙 (postcompose H (vcomp θ ψ)) := (postcomposeVcompIso H θ ψ).inv_hom_id

section Graded
variable [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [∀ a b : C, GradedSupercategory R (a ⟶ b)]

theorem postcomposeVcompIso_hom_isHomogeneous (hH : H.IsGraded) :
    (postcomposeVcompIso H θ ψ).hom.IsHomogeneous 0 0 :=
  fun a => ⟨H.mapComp_hom_mem (θ.X a) (ψ.X a),
    hH.mapComp_hom_mem_degree (θ.X a) (ψ.X a)⟩

theorem postcomposeVcompIso_inv_isHomogeneous (hH : H.IsGraded) :
    (postcomposeVcompIso H θ ψ).inv.IsHomogeneous 0 0 := by
  intro a
  exact ⟨inv_mem _ (H.mapComp_hom_mem _ _), by
    simpa only [neg_zero] using! GradedSupercategory.inv_mem_degree
      (H.mapComp (θ.X a) (ψ.X a)) (hH.mapComp_hom_mem_degree _ _)⟩
end Graded
end TwoNatTrans
end StringDiagrams
