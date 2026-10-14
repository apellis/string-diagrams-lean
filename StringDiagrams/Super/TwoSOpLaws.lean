import StringDiagrams.Super.TwoSOp

/-!
# The 2-super-opposite is a 2-supercategory

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 3.4:
`𝔄^{sop}` satisfies the axioms of a 2-supercategory, including the super interchange law
(`TwoSOp.twoSupercategory`).
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
universe r u v w
namespace TwoSOp
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

include R in
private theorem triangle_inverse {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (leftUnitor g).inv ≫ (associator f (𝟙 b) g).inv = (rightUnitor f).inv ▷ g := by
  have h : (associator f (𝟙 b) g) ≪≫ whiskerLeftIso (R := R) f (leftUnitor g) =
      whiskerRightIso (R := R) (rightUnitor f) g := Iso.ext (triangle (R := R) f g)
  exact congrArg Iso.inv h

instance twoSupercategory : TwoSupercategory R (TwoSOp R B) where
  whiskerLeft_id f g := (TwoSOpAux.leftSOp (R := R) (SOp.unop f)).map_id g
  whiskerLeft_comp f _ _ _ η θ := (TwoSOpAux.leftSOp (R := R) (SOp.unop f)).map_comp η θ
  id_whiskerLeft {a _ f g} η := by
    apply SOp.hom_ext
    change 𝟙 a.unop ◁ SOp.unsop η = SOp.compC (R := R) (leftUnitor (SOp.unop f)).inv
      (SOp.compC (R := R) (SOp.unsop η) (leftUnitor (SOp.unop g)).hom)
    rw [SOp.compC_even_left (inv_mem _ (leftUnitor_hom_mem _)),
      SOp.compC_even_right _ (leftUnitor_hom_mem _)]
    simpa only [Category.assoc] using id_whiskerLeft (R := R) (SOp.unsop η)
  comp_whiskerLeft f g h h' η := by
    apply SOp.hom_ext
    change (SOp.unop f ≫ SOp.unop g) ◁ SOp.unsop η =
      SOp.compC (R := R) (associator (SOp.unop f) (SOp.unop g) (SOp.unop h)).inv
        (SOp.compC (R := R) (SOp.unop f ◁ SOp.unop g ◁ SOp.unsop η)
          (associator (SOp.unop f) (SOp.unop g) (SOp.unop h')).hom)
    rw [SOp.compC_even_left (inv_mem _ (associator_hom_mem _ _ _)),
      SOp.compC_even_right _ (associator_hom_mem _ _ _)]
    simpa only [Category.assoc] using comp_whiskerLeft (R := R)
      (SOp.unop f) (SOp.unop g) (SOp.unsop η)
  id_whiskerRight f g := (TwoSOpAux.rightSOp (R := R) (SOp.unop g)).map_id f
  comp_whiskerRight η θ i := (TwoSOpAux.rightSOp (R := R) (SOp.unop i)).map_comp η θ
  whiskerRight_id {_ b f g} η := by
    apply SOp.hom_ext
    change SOp.unsop η ▷ 𝟙 b.unop = SOp.compC (R := R) (rightUnitor (SOp.unop f)).inv
      (SOp.compC (R := R) (SOp.unsop η) (rightUnitor (SOp.unop g)).hom)
    rw [SOp.compC_even_left (inv_mem _ (rightUnitor_hom_mem _)),
      SOp.compC_even_right _ (rightUnitor_hom_mem _)]
    simpa only [Category.assoc] using whiskerRight_id (R := R) (SOp.unsop η)
  whiskerRight_comp {_ _ _ _ f f'} η g h := by
    apply SOp.hom_ext
    change SOp.unsop η ▷ (SOp.unop g ≫ SOp.unop h) =
      SOp.compC (R := R) (associator (SOp.unop f) (SOp.unop g) (SOp.unop h)).hom
        (SOp.compC (R := R) (SOp.unsop η ▷ SOp.unop g ▷ SOp.unop h)
          (associator (SOp.unop f') (SOp.unop g) (SOp.unop h)).inv)
    rw [SOp.compC_even_left (associator_hom_mem _ _ _),
      SOp.compC_even_right _ (inv_mem _ (associator_hom_mem _ _ _))]
    simpa only [Category.assoc] using whiskerRight_comp (R := R)
      (SOp.unsop η) (SOp.unop g) (SOp.unop h)
  whisker_assoc f g g' η h := by
    apply SOp.hom_ext
    change (SOp.unop f ◁ SOp.unsop η) ▷ SOp.unop h =
      SOp.compC (R := R) (associator (SOp.unop f) (SOp.unop g) (SOp.unop h)).inv
        (SOp.compC (R := R) (SOp.unop f ◁ (SOp.unsop η ▷ SOp.unop h))
          (associator (SOp.unop f) (SOp.unop g') (SOp.unop h)).hom)
    rw [SOp.compC_even_left (inv_mem _ (associator_hom_mem _ _ _)),
      SOp.compC_even_right _ (associator_hom_mem _ _ _)]
    simpa only [Category.assoc] using whisker_assoc (R := R)
      (SOp.unop f) (SOp.unsop η) (SOp.unop h)
  pentagon f g h i := by
    apply SOp.hom_ext
    change SOp.compC (R := R)
      ((associator (SOp.unop f) (SOp.unop g) (SOp.unop h)).inv ▷ SOp.unop i)
      (SOp.compC (R := R)
        (associator (SOp.unop f) (SOp.unop g ≫ SOp.unop h) (SOp.unop i)).inv
        (SOp.unop f ◁ (associator (SOp.unop g) (SOp.unop h) (SOp.unop i)).inv)) =
      SOp.compC (R := R)
        (associator (SOp.unop f ≫ SOp.unop g) (SOp.unop h) (SOp.unop i)).inv
        (associator (SOp.unop f) (SOp.unop g) (SOp.unop h ≫ SOp.unop i)).inv
    rw [SOp.compC_even_left (whiskerRight_mem _ (inv_mem _ (associator_hom_mem _ _ _))),
      SOp.compC_even_left (inv_mem _ (associator_hom_mem _ _ _)),
      SOp.compC_even_left (inv_mem _ (associator_hom_mem _ _ _))]
    simpa only [Category.assoc] using pentagon_inv R
      (SOp.unop f) (SOp.unop g) (SOp.unop h) (SOp.unop i)
  triangle {_ b _} f g := by
    apply SOp.hom_ext
    change SOp.compC (R := R) (associator (SOp.unop f) (𝟙 b.unop) (SOp.unop g)).inv
      (SOp.unop f ◁ (leftUnitor (SOp.unop g)).inv) =
      (rightUnitor (SOp.unop f)).inv ▷ SOp.unop g
    rw [SOp.compC_even_left (inv_mem _ (associator_hom_mem _ _ _))]
    exact triangle_inverse (R := R) (SOp.unop f) (SOp.unop g)
  whiskerLeft_add f _ _ η θ := SOp.hom_ext (whiskerLeft_add (R := R)
    (SOp.unop f) (SOp.unsop η) (SOp.unsop θ))
  add_whiskerRight η θ h := SOp.hom_ext (add_whiskerRight (R := R)
    (SOp.unsop η) (SOp.unsop θ) (SOp.unop h))
  whiskerLeft_smul f _ _ s η := SOp.hom_ext (whiskerLeft_smul (SOp.unop f) s (SOp.unsop η))
  smul_whiskerRight s η h := SOp.hom_ext (smul_whiskerRight s (SOp.unsop η) (SOp.unop h))
  whiskerLeft_mem f _ _ _ _ hη := whiskerLeft_mem (SOp.unop f) hη
  whiskerRight_mem h hη := whiskerRight_mem (SOp.unop h) hη
  super_interchange {_ _ _ f g h i p q η θ} hη hθ := by
    change SOp.unsop η ∈ parity (R := R) (SOp.unop g) (SOp.unop f) p at hη
    change SOp.unsop θ ∈ parity (R := R) (SOp.unop i) (SOp.unop h) q at hθ
    apply SOp.hom_ext
    rw [koszulSign_smul (R := R), SOp.unsop_smul]
    change SOp.compC (R := R) (SOp.unsop η ▷ SOp.unop h) (SOp.unop g ◁ SOp.unsop θ) =
      sign R (p * q) • SOp.compC (R := R)
        (SOp.unop f ◁ SOp.unsop θ) (SOp.unsop η ▷ SOp.unop i)
    rw [SOp.compC_of_mem (whiskerRight_mem (SOp.unop h) hη)
      (whiskerLeft_mem (SOp.unop g) hθ)]
    rw [SOp.compC_of_mem (whiskerLeft_mem (SOp.unop f) hθ)
      (whiskerRight_mem (SOp.unop i) hη)]
    rw [mul_comm q p, sign_smul_sign_smul]
    exact (show SOp.unsop η ▷ SOp.unop i ≫ SOp.unop f ◁ SOp.unsop θ =
      sign R (p * q) • (SOp.unop g ◁ SOp.unsop θ ≫ SOp.unsop η ▷ SOp.unop h) from
        (super_interchange (R := R) hη hθ).trans (koszulSign_smul p q _)).symm
  associator_hom_mem f g h := inv_mem _ (associator_hom_mem (R := R)
    (SOp.unop f) (SOp.unop g) (SOp.unop h))
  leftUnitor_hom_mem f := inv_mem _ (leftUnitor_hom_mem (R := R) (SOp.unop f))
  rightUnitor_hom_mem f := inv_mem _ (rightUnitor_hom_mem (R := R) (SOp.unop f))
end TwoSOp
end StringDiagrams
