import StringDiagrams.Super.TwoFunctorPrecomposition

/-!
# Postcomposition of actual 2-natural transformations

Postcomposition retains the compositor of an arbitrary 2-superfunctor. All
naturality proofs below apply to every 2-morphism, not only the even ones.
Composition and unit coherence are proved directly from the 2-superfunctor
constraints, without a strictness assumption or an even-only bridge.
This supplies the right-whiskered counit leg, not the full counit paste law.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ w
variable {R : Type w} [CommRing R]
  {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)]
  {B : Type u₂} [BicategoryStruct.{w₂, v₂} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₃} [BicategoryStruct.{w₃, v₃} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

namespace TwoNatTrans
variable (H : TwoSuperfunctor R B C) {F G : TwoSuperfunctor R A B}

/-- The structure map of postcomposition, with both compositor factors. -/
def postcomposeCell (θ : TwoNatTrans F G) {a b : A} (f : a ⟶ b) :
    H.map (F.map f) ≫ H.map (θ.X b) ⟶ H.map (θ.X a) ≫ H.map (G.map f) :=
  (H.mapComp (F.map f) (θ.X b)).hom ≫ H.map₂ (θ.x f) ≫
    (H.mapComp (θ.X a) (G.map f)).inv

omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- Naturality holds without a parity restriction on the input 2-morphism. -/
theorem postcomposeCell_naturality (θ : TwoNatTrans F G) {a b : A}
    {f g : a ⟶ b} (η : f ⟶ g) :
    H.map₂ (F.map₂ η) ▷ H.map (θ.X b) ≫ postcomposeCell H θ g =
      postcomposeCell H θ f ≫ H.map (θ.X a) ◁ H.map₂ (G.map₂ η) := by
  unfold postcomposeCell
  rw [← cancel_mono (H.mapComp (θ.X a) (G.map g)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [H.mapComp_naturality_left_assoc, ← H.map₂_comp, θ.naturality,
    H.map₂_comp, H.mapComp_naturality_right, Iso.inv_hom_id_assoc]

omit [TwoSupercategory R B] [TwoSupercategory R C] in
private theorem map_associator_hom {a b c d : B} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) :
    (BicategoryStruct.associator (H.map f) (H.map g) (H.map h)).hom ≫
      H.map f ◁ (H.mapComp g h).hom ≫ (H.mapComp f (g ≫ h)).hom =
    (H.mapComp f g).hom ▷ H.map h ≫ (H.mapComp (f ≫ g) h).hom ≫
      H.map₂ (BicategoryStruct.associator f g h).hom := by
  rw [← cancel_mono (H.map₂Iso (BicategoryStruct.associator f g h)).inv]
  simp only [Category.assoc, TwoSuperfunctor.map₂Iso_inv, ← H.map₂_comp,
    Iso.hom_inv_id, H.map₂_id, Category.comp_id]
  rw [H.map₂_associator, Iso.hom_inv_id_assoc]

omit [TwoSupercategory R B] [TwoSupercategory R C] in
private theorem map_leftUnitor_inv {a b : B} (f : a ⟶ b) :
    (BicategoryStruct.leftUnitor (H.map f)).inv ≫
      (H.mapId a).hom ▷ H.map f ≫ (H.mapComp (𝟙 a) f).hom =
    H.map₂ (BicategoryStruct.leftUnitor f).inv := by
  rw [← cancel_mono (H.map₂Iso (BicategoryStruct.leftUnitor f)).hom]
  simp only [Category.assoc, TwoSuperfunctor.map₂Iso_hom, ← H.map₂_comp,
    Iso.inv_hom_id, H.map₂_id]
  rw [H.map₂_leftUnitor, Iso.inv_hom_id]

/-- Postcompose an actual transformation, including composition and unit coherence. -/
def postcompose (θ : TwoNatTrans F G) : TwoNatTrans (F.comp H) (G.comp H) where
  X a := H.map (θ.X a)
  x f := postcomposeCell H θ f
  x_mem f := by
    change postcomposeCell H θ f ∈ parity (R := R) _ _ 0
    simpa only [postcomposeCell, add_zero] using comp_mem (H.mapComp_hom_mem (F.map f) (θ.X _))
      (comp_mem (H.map₂_mem (θ.x_mem f))
        (inv_mem _ (H.mapComp_hom_mem (θ.X _) (G.map f))))
  naturality η := postcomposeCell_naturality H θ η
  x_comp f g := by
    simp only [TwoSuperfunctor.comp, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom,
      postcomposeCell, comp_whiskerRight (R := R), whiskerLeft_comp (R := R), Category.assoc]
    rw [← cancel_mono (H.mapComp (θ.X _) (G.map (f ≫ g))).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [H.mapComp_naturality_right]
    rw [reassoc_of% (map_associator_hom H (θ.X _) (G.map f) (G.map g)),
      inv_hom_whiskerRight_assoc R, H.mapComp_naturality_left_assoc,
      H.mapComp_naturality_left_assoc, ← H.map₂_associator_assoc,
      whiskerLeft_inv_hom_assoc R, H.mapComp_naturality_right_assoc,
      reassoc_of% (map_associator_hom H (F.map f) (F.map g) (θ.X _))]
    simp only [← H.map₂_comp]
    rw [θ.x_comp]
  x_id a := by
    simp only [TwoSuperfunctor.comp, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom,
      postcomposeCell, comp_whiskerRight (R := R), whiskerLeft_comp (R := R), Category.assoc]
    rw [← cancel_mono (H.mapComp (θ.X a) (G.map (𝟙 a))).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [H.mapComp_naturality_left_assoc,
      reassoc_of% (map_leftUnitor_inv H (θ.X a)), ← H.map₂_rightUnitor (θ.X a)]
    simp only [Category.assoc, ← H.map₂_comp]
    rw [θ.x_id, H.mapComp_naturality_right]

omit [TwoSupercategory R B] in
@[simp] theorem postcompose_X (θ : TwoNatTrans F G) (a : A) :
    (postcompose H θ).X a = H.map (θ.X a) := rfl

omit [TwoSupercategory R B] in
@[simp] theorem postcompose_x (θ : TwoNatTrans F G) {a b : A} (f : a ⟶ b) :
    (postcompose H θ).x f = (H.mapComp (F.map f) (θ.X b)).hom ≫
      H.map₂ (θ.x f) ≫ (H.mapComp (θ.X a) (G.map f)).inv := rfl

omit [TwoSupercategory R B] in
theorem postcompose_isStrong {θ : TwoNatTrans F G} (hθ : θ.IsStrong) :
    (postcompose H θ).IsStrong := by
  intro a b f
  let := hθ f
  have : IsIso (H.map₂ (θ.x f)) :=
    (H.mapFunctor _ _).map_isIso (θ.x f)
  change IsIso ((H.mapComp (F.map f) (θ.X b)).hom ≫
    H.map₂ (θ.x f) ≫ (H.mapComp (θ.X a) (G.map f)).inv)
  infer_instance

/-- Postcomposition acts on actual modifications of either parity. -/
def postcomposeModification {θ ψ : TwoNatTrans F G} (α : θ ⟶ ψ) :
    postcompose H θ ⟶ postcompose H ψ where
  app a := H.map₂ (α.app a)
  naturality {a b} f := by
    change postcomposeCell H θ f ≫ H.map₂ (α.app a) ▷ H.map (G.map f) =
      H.map (F.map f) ◁ H.map₂ (α.app b) ≫ postcomposeCell H ψ f
    unfold postcomposeCell
    rw [← cancel_mono (H.mapComp (ψ.X a) (G.map f)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [H.mapComp_naturality_left, Iso.inv_hom_id_assoc,
      ← H.map₂_comp, α.naturality, H.map₂_comp,
      H.mapComp_naturality_right_assoc]

@[simp] theorem postcomposeModification_app {θ ψ : TwoNatTrans F G}
    (α : θ ⟶ ψ) (a : A) : (postcomposeModification H α).app a = H.map₂ (α.app a) := rfl

/-- Postcomposition on the category of transformations and supermodifications. -/
def postcomposition (F G : TwoSuperfunctor R A B) :
    TwoNatTrans F G ⥤ TwoNatTrans (F.comp H) (G.comp H) where
  obj := postcompose H
  map := postcomposeModification H
  map_id θ := by ext a; exact H.map₂_id (θ.X a)
  map_comp α β := by ext a; exact H.map₂_comp (α.app a) (β.app a)

instance (F G : TwoSuperfunctor R A B) : (postcomposition H F G).Additive where
  map_add := by intros; ext a; exact H.map₂_add _ _

instance (F G : TwoSuperfunctor R A B) : (postcomposition H F G).Linear R where
  map_smul α r := by ext a; exact H.map₂_smul r (α.app a)

/-- Parity preservation does not need a grading hypothesis. -/
theorem postcomposeModification_mem {θ ψ : TwoNatTrans F G} {α : θ ⟶ ψ}
    {p : ZMod 2} (hα : ∀ a, α.app a ∈ parity (R := R) _ _ p) :
    ∀ a, (postcomposeModification H α).app a ∈ parity (R := R) _ _ p :=
  fun a => H.map₂_mem (hα a)

instance (F G : TwoSuperfunctor R A B) : IsSuperfunctor R (postcomposition H F G) where
  map_mem hα := postcomposeModification_mem H hα

section Graded
variable [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [∀ a b : C, GradedSupercategory R (a ⟶ b)]

omit [TwoSupercategory R B] in
theorem postcompose_isGraded (hH : H.IsGraded) {θ : TwoNatTrans F G}
    (hθ : θ.IsGraded) : (postcompose H θ).IsGraded := by
  intro a b f
  change postcomposeCell H θ f ∈ GradedSupercategory.degree (R := R) _ _ 0
  simpa only [postcomposeCell, add_zero, neg_zero] using
    GradedSupercategory.comp_mem_degree (hH.mapComp_hom_mem_degree (F.map f) (θ.X b))
      (GradedSupercategory.comp_mem_degree (hH.map₂_mem_degree (hθ f))
        (GradedSupercategory.inv_mem_degree _ (hH.mapComp_hom_mem_degree (θ.X a) (G.map f))))

theorem postcomposeModification_isHomogeneous (hH : H.IsGraded)
    {θ ψ : TwoNatTrans F G} {α : θ ⟶ ψ} {p : ZMod 2} {n : ℤ}
    (hα : α.IsHomogeneous p n) : (postcomposeModification H α).IsHomogeneous p n :=
  fun a => ⟨H.map₂_mem (hα a).1, hH.map₂_mem_degree (hα a).2⟩
end Graded
end TwoNatTrans
end StringDiagrams
