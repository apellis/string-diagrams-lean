import StringDiagrams.Super.GradedTwoEnvelopeCounitComposition

/-!
# Precomposition of actual 2-natural transformations

Precomposition by an arbitrary 2-superfunctor retains its nontrivial composition
and identity constraints. Naturality is checked for every 2-morphism, including
odd ones. This supplies the left-whiskered leg of a composite counit square;
it does not assert the full functor-composition coherence of the counit.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ w
variable {R : Type w} [CommRing R]
  {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)]
  {B : Type u₂} [BicategoryStruct.{w₂, v₂} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]
  {C : Type u₃} [BicategoryStruct.{w₃, v₃} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

namespace TwoNatTrans
variable (P : TwoSuperfunctor R A B) {F G : TwoSuperfunctor R B C}

/-- Precompose an actual transformation, including all coherence fields. -/
def precompose (θ : TwoNatTrans F G) : TwoNatTrans (P.comp F) (P.comp G) where
  X a := θ.X (P.obj a)
  x f := θ.x (P.map f)
  x_mem f := θ.x_mem (P.map f)
  naturality η := θ.naturality (P.map₂ η)
  x_comp f g := by
    change ((F.mapComp (P.map f) (P.map g)).hom ≫ F.map₂ (P.mapComp f g).hom) ▷
      θ.X _ ≫ θ.x (P.map (f ≫ g)) = _
    rw [comp_whiskerRight (R := R), Category.assoc, θ.naturality,
      ← Category.assoc, θ.x_comp]
    simp only [TwoSuperfunctor.comp, Iso.trans_hom, whiskerLeft_comp (R := R), Category.assoc]
    rfl
  x_id a := by
    change (BicategoryStruct.rightUnitor (θ.X (P.obj a))).hom ≫
      (BicategoryStruct.leftUnitor (θ.X (P.obj a))).inv ≫
      ((F.mapId (P.obj a)).hom ≫ F.map₂ (P.mapId a).hom) ▷ θ.X (P.obj a) ≫
      θ.x (P.map (𝟙 a)) = _
    simp only [comp_whiskerRight (R := R), Category.assoc]
    rw [θ.naturality, θ.x_id_assoc]
    simp only [TwoSuperfunctor.comp, Iso.trans_hom, whiskerLeft_comp (R := R)]
    rfl

@[simp] theorem precompose_X (θ : TwoNatTrans F G) (a : A) :
    (precompose P θ).X a = θ.X (P.obj a) := rfl

@[simp] theorem precompose_x (θ : TwoNatTrans F G) {a b : A} (f : a ⟶ b) :
    (precompose P θ).x f = θ.x (P.map f) := rfl

theorem precompose_isStrong {θ : TwoNatTrans F G} (hθ : θ.IsStrong) :
    (precompose P θ).IsStrong := fun f => hθ (P.map f)

/-- Precomposition of supermodifications retains the actual component maps. -/
def precomposeModification {θ ψ : TwoNatTrans F G} (α : θ ⟶ ψ) :
    precompose P θ ⟶ precompose P ψ where
  app a := α.app (P.obj a)
  naturality f := α.naturality (P.map f)

/-- Precomposition on the whole category of transformations and supermodifications. -/
def precomposition (F G : TwoSuperfunctor R B C) :
    TwoNatTrans F G ⥤ TwoNatTrans (P.comp F) (P.comp G) where
  obj := precompose P
  map := precomposeModification P
  map_id _ := rfl
  map_comp _ _ := rfl

section Graded
variable [∀ a b : C, GradedSupercategory R (a ⟶ b)]

theorem precompose_isGraded {θ : TwoNatTrans F G} (hθ : θ.IsGraded) :
    (precompose P θ).IsGraded := fun f => hθ (P.map f)

theorem precomposeModification_isHomogeneous {θ ψ : TwoNatTrans F G}
    {α : θ ⟶ ψ} {p : ZMod 2} {n : ℤ} (hα : α.IsHomogeneous p n) :
    (precomposeModification P α).IsHomogeneous p n := fun a => hα (P.obj a)
end Graded
end TwoNatTrans
end StringDiagrams
