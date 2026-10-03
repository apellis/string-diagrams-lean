import StringDiagrams.Super.GradedTwoEnvelopeTransformation

/-!
# The hom 2-supercategory of graded 2-superfunctors

`GradedTwoHom R B C` has graded 2-superfunctors as objects, **all** graded oplax
`TwoNatTrans` as 1-morphisms, and all supermodifications as 2-morphisms. Its signed
interchange and coherence are inherited componentwise from `C`. No strongness
condition is imposed on transformations.

This is a 2-supercategory, not an assertion of a direct-sum integer grading on
its entire modification spaces: over infinitely many objects, componentwise
finite degree support need not be uniformly finite. Bidegrees are expressed by
`Supermodification.IsHomogeneous`. The concrete consumer is the graded envelope
hom 2-superequivalence in `GradedTwoEnvelopeTwoHom`.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁ w₂ v₂ u₂

variable (R : Type w) [CommRing R]
  (B : Type u₁) [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  (C : Type u₂) [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]

/-- Graded 2-superfunctors, with no strictness assumption. -/
structure GradedTwoHom where
  toTwoSuperfunctor : TwoSuperfunctor R B C
  isGraded : toTwoSuperfunctor.IsGraded

namespace GradedTwoHom
variable {R B C} [TwoSupercategory R C]

/-- All degree-zero-coherent oplax transformations; their coherence need not be invertible. -/
abbrev Hom (F G : GradedTwoHom R B C) :=
  {θ : TwoNatTrans F.toTwoSuperfunctor G.toTwoSuperfunctor // θ.IsGraded}

instance (F G : GradedTwoHom R B C) : Category (Hom F G) where
  Hom θ ψ := θ.val ⟶ ψ.val
  id θ := 𝟙 θ.val
  comp α β := α ≫ β
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

instance (F G : GradedTwoHom R B C) : Preadditive (Hom F G) where
  homGroup θ ψ := inferInstanceAs (AddCommGroup (θ.val ⟶ ψ.val))
  add_comp θ ψ φ := Preadditive.add_comp θ.val ψ.val φ.val
  comp_add θ ψ φ := Preadditive.comp_add θ.val ψ.val φ.val

instance (F G : GradedTwoHom R B C) : Linear R (Hom F G) where
  homModule θ ψ := inferInstanceAs (Module R (θ.val ⟶ ψ.val))
  smul_comp θ ψ φ := Linear.smul_comp θ.val ψ.val φ.val
  comp_smul θ ψ φ := Linear.comp_smul θ.val ψ.val φ.val

instance (F G : GradedTwoHom R B C) : Supercategory R (Hom F G) where
  parity θ ψ := parity (R := R) θ.val ψ.val
  isInternal θ ψ := Supercategory.isInternal θ.val ψ.val
  id_mem θ := Supercategory.id_mem θ.val
  comp_mem := Supercategory.comp_mem

/-- Lift an isomorphism of the underlying transformations to the full hom subcategory. -/
def isoMk {F G : GradedTwoHom R B C} {θ ψ : Hom F G} (e : θ.val ≅ ψ.val) : θ ≅ ψ where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

variable [TwoSupercategory R B] [GradedTwoSupercategory R C]

instance : BicategoryStruct (GradedTwoHom R B C) where
  Hom := Hom
  id F := ⟨TwoNatTrans.id F.toTwoSuperfunctor, TwoNatTrans.id_isGraded⟩
  comp θ ψ := ⟨TwoNatTrans.vcomp θ.val ψ.val, TwoNatTrans.IsGraded.vcomp θ.property ψ.property⟩
  homCategory _ _ := inferInstance
  whiskerLeft θ _ _ α := TwoNatTrans.whiskerLeft θ.val α
  whiskerRight α ψ := TwoNatTrans.whiskerRight α ψ.val
  associator θ ψ φ := isoMk (TwoNatTrans.associator θ.val ψ.val φ.val)
  leftUnitor θ := isoMk (TwoNatTrans.leftUnitor θ.val)
  rightUnitor θ := isoMk (TwoNatTrans.rightUnitor θ.val)

instance (F G : GradedTwoHom R B C) : Preadditive (F ⟶ G) :=
  inferInstanceAs (Preadditive (Hom F G))
instance (F G : GradedTwoHom R B C) : Linear R (F ⟶ G) :=
  inferInstanceAs (Linear R (Hom F G))
instance (F G : GradedTwoHom R B C) : Supercategory R (F ⟶ G) :=
  inferInstanceAs (Supercategory R (Hom F G))

/-- The actual signed hom 2-supercategory, retaining arbitrary modifications. -/
instance : TwoSupercategory R (GradedTwoHom R B C) where
  whiskerLeft_id _ _ := TwoNatTrans.hom_ext fun _ => whiskerLeft_id (R := R) _ _
  whiskerLeft_comp _ _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => whiskerLeft_comp (R := R) _ _ _
  id_whiskerLeft _ := TwoNatTrans.hom_ext fun _ => id_whiskerLeft (R := R) _
  comp_whiskerLeft _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => comp_whiskerLeft (R := R) _ _ _
  id_whiskerRight _ _ := TwoNatTrans.hom_ext fun _ => id_whiskerRight (R := R) _ _
  comp_whiskerRight _ _ _ := TwoNatTrans.hom_ext fun _ => comp_whiskerRight (R := R) _ _ _
  whiskerRight_id _ := TwoNatTrans.hom_ext fun _ => whiskerRight_id (R := R) _
  whiskerRight_comp _ _ _ := TwoNatTrans.hom_ext fun _ => whiskerRight_comp (R := R) _ _ _
  whisker_assoc _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => whisker_assoc (R := R) _ _ _
  pentagon _ _ _ _ := TwoNatTrans.hom_ext fun _ => pentagon (R := R) _ _ _ _
  triangle _ _ := TwoNatTrans.hom_ext fun _ => triangle (R := R) _ _
  whiskerLeft_add _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => whiskerLeft_add (R := R) _ _ _
  add_whiskerRight _ _ _ := TwoNatTrans.hom_ext fun _ => add_whiskerRight (R := R) _ _ _
  whiskerLeft_smul _ _ _ r _ := TwoNatTrans.hom_ext fun _ => whiskerLeft_smul (R := R) _ r _
  smul_whiskerRight r _ _ := TwoNatTrans.hom_ext fun _ => smul_whiskerRight (R := R) r _ _
  whiskerLeft_mem _ _ _ _ _ hα a := whiskerLeft_mem _ (hα a)
  whiskerRight_mem _ hα a := whiskerRight_mem _ (hα a)
  super_interchange hα hβ := TwoNatTrans.hom_ext fun a => super_interchange (hα a) (hβ a)
  associator_hom_mem _ _ _ _ := associator_hom_mem (R := R) _ _ _
  leftUnitor_hom_mem _ _ := leftUnitor_hom_mem (R := R) _
  rightUnitor_hom_mem _ _ := rightUnitor_hom_mem (R := R) _

end GradedTwoHom
end StringDiagrams
end
