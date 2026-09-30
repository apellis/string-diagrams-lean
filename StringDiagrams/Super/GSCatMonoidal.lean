import StringDiagrams.Super.BoxProductGraded

/-!
# The monoidal category `(GSCat, ⊠, I)`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (after
Definition 6.1): "Let `GSCat` be the category of all graded supercategories and graded
superfunctors. We make `GSCat` into a monoidal category with tensor product operation `− ⊠ −`
defined in just the same way as was explained after Example 1.2."

## Main definitions

* `GSCat.instCategory`: the category `GSCat R` of graded supercategories and graded
  superfunctors (the underlying category of the strict graded 2-supercategory `𝔊𝔖ℭ𝔞𝔱` of
  `StringDiagrams.Super.GSCat`), with the faithful forgetful functor `GSCat.forget R` to
  `SCat R`.
* `GSCat.instMonoidalCategory`: **the monoidal category `(GSCat, ⊠, I)`**, for graded
  supercategories with morphism modules in the universe of `k` (`GSCat.{u, u, w} k`,
  `k : Type u`): `A ⊗ B := A ⊠ B` (the graded supercategory `BoxProd.instGradedSupercategory`),
  `F ⊗ G := F ⊠ G` (`BoxProd.gradedMap`), unit `I` (`BoxUnit k`, all morphisms of degree `0`),
  and the associator and unitors of `BoxProd`, which are graded superfunctors
  (`BoxProd.gradedAssoc`, `BoxProd.gradedLunit`, `BoxProd.gradedRunit` and their inverses).
  The forgetful functor to `(SCat, ⊠, I)` is strict monoidal (`GSCat.forget_obj_tensorObj`,
  `GSCat.forget_map_tensorHom`, `GSCat.forget_map_associator_hom`, …), and the axioms are
  transported from `SCat.instMonoidalCategory` along it.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w v u

namespace GSCat

section Category

variable {R : Type w} [CommRing R]

/-- The category `GSCat` of graded supercategories and graded superfunctors (Brundan–Ellis,
§6, after Definition 6.1): the underlying category of the strict graded 2-supercategory
`𝔊𝔖ℭ𝔞𝔱`. -/
instance instCategory : Category (GSCat.{w, v, u} R) where
  toCategoryStruct := (inferInstance : BicategoryStruct (GSCat.{w, v, u} R)).toCategoryStruct
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable (R) in
/-- The forgetful functor `GSCat → SCat`: a graded supercategory is a supercategory, and a
graded superfunctor is a superfunctor. -/
def forget : GSCat.{w, v, u} R ⥤ SCat.{w, v, u} R where
  obj A := A.toSCat
  map F := F.as.toSuperfunctor

@[simp] theorem forget_obj (A : GSCat.{w, v, u} R) : (forget R).obj A = A.toSCat := rfl

@[simp] theorem forget_map {A B : GSCat.{w, v, u} R} (F : A ⟶ B) :
    (forget R).map F = F.as.toSuperfunctor := rfl

/-- Morphisms of `GSCat` with the same underlying superfunctor are equal. -/
theorem hom_ext {A B : GSCat.{w, v, u} R} {F G : A ⟶ B}
    (h : (forget R).map F = (forget R).map G) : F = G := by
  obtain ⟨⟨F, _⟩⟩ := F
  obtain ⟨⟨G, _⟩⟩ := G
  change F = G at h
  subst h
  rfl

instance : (forget R).Faithful where
  map_injective h := hom_ext h

end Category

open MonoidalCategory BoxProd

variable {k : Type u} [CommRing k]

/-- The data of the monoidal structure `⊠` on the category `GSCat` of graded supercategories
(with morphism modules in the universe of `k`) and graded superfunctors: `A ⊗ B := A ⊠ B`,
`F ⊗ G := F ⊠ G`, unit `I`, and the associator and unitors of `BoxProd`, which are
isomorphisms of graded supercategories. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (GSCat.{u, u, w} k) where
  tensorObj A B := GSCat.of k (BoxProd k A B)
  whiskerLeft A _ _ G := ⟨gradedMap (GradedSuperfunctor.id k A) G.as⟩
  whiskerRight F B := ⟨gradedMap F.as (GradedSuperfunctor.id k B)⟩
  tensorHom F G := ⟨gradedMap F.as G.as⟩
  tensorUnit := GSCat.of k (BoxUnit.{w, u} k)
  associator A B C :=
    ⟨⟨gradedAssoc A B C⟩, ⟨gradedAssocInv A B C⟩,
      hom_ext (α_ A.toSCat B.toSCat C.toSCat).hom_inv_id,
      hom_ext (α_ A.toSCat B.toSCat C.toSCat).inv_hom_id⟩
  leftUnitor A := ⟨⟨gradedLunit A⟩, ⟨gradedLunitInv A⟩, hom_ext (λ_ A.toSCat).hom_inv_id,
    hom_ext (λ_ A.toSCat).inv_hom_id⟩
  rightUnitor A := ⟨⟨gradedRunit A⟩, ⟨gradedRunitInv A⟩, hom_ext (ρ_ A.toSCat).hom_inv_id,
    hom_ext (ρ_ A.toSCat).inv_hom_id⟩

theorem tensorObj_def (A B : GSCat.{u, u, w} k) : A ⊗ B = GSCat.of k (BoxProd k A B) := rfl

theorem tensorUnit_def : 𝟙_ (GSCat.{u, u, w} k) = GSCat.of k (BoxUnit.{w, u} k) := rfl

/-! ### The forgetful functor to `SCat` is strict monoidal -/

@[simp] theorem forget_obj_tensorObj (A B : GSCat.{u, u, w} k) :
    (forget k).obj (A ⊗ B) = (forget k).obj A ⊗ (forget k).obj B := rfl

@[simp] theorem forget_obj_tensorUnit : (forget k).obj (𝟙_ (GSCat.{u, u, w} k)) = 𝟙_ _ := rfl

@[simp] theorem forget_map_tensorHom {A B A' B' : GSCat.{u, u, w} k} (F : A ⟶ A') (G : B ⟶ B') :
    (forget k).map (F ⊗ₘ G) = (forget k).map F ⊗ₘ (forget k).map G := rfl

@[simp] theorem forget_map_whiskerLeft (A : GSCat.{u, u, w} k) {B B' : GSCat.{u, u, w} k}
    (G : B ⟶ B') : (forget k).map (A ◁ G) = (forget k).obj A ◁ (forget k).map G := rfl

@[simp] theorem forget_map_whiskerRight {A A' : GSCat.{u, u, w} k} (F : A ⟶ A')
    (B : GSCat.{u, u, w} k) : (forget k).map (F ▷ B) = (forget k).map F ▷ (forget k).obj B :=
  rfl

@[simp] theorem forget_map_associator_hom (A B C : GSCat.{u, u, w} k) :
    (forget k).map (α_ A B C).hom =
      (α_ ((forget k).obj A) ((forget k).obj B) ((forget k).obj C)).hom := rfl

@[simp] theorem forget_map_associator_inv (A B C : GSCat.{u, u, w} k) :
    (forget k).map (α_ A B C).inv =
      (α_ ((forget k).obj A) ((forget k).obj B) ((forget k).obj C)).inv := rfl

@[simp] theorem forget_map_leftUnitor_hom (A : GSCat.{u, u, w} k) :
    (forget k).map (λ_ A).hom = (λ_ ((forget k).obj A)).hom := rfl

@[simp] theorem forget_map_leftUnitor_inv (A : GSCat.{u, u, w} k) :
    (forget k).map (λ_ A).inv = (λ_ ((forget k).obj A)).inv := rfl

@[simp] theorem forget_map_rightUnitor_hom (A : GSCat.{u, u, w} k) :
    (forget k).map (ρ_ A).hom = (ρ_ ((forget k).obj A)).hom := rfl

@[simp] theorem forget_map_rightUnitor_inv (A : GSCat.{u, u, w} k) :
    (forget k).map (ρ_ A).inv = (ρ_ ((forget k).obj A)).inv := rfl

/-- **Brundan–Ellis, §6 (after Definition 6.1).** `⊠` makes the category `GSCat` of graded
supercategories (with morphism modules in the universe of `k`) and graded superfunctors into a
monoidal category. The axioms hold on the underlying superfunctors by
`SCat.instMonoidalCategory`. -/
instance instMonoidalCategory : MonoidalCategory (GSCat.{u, u, w} k) where
  tensorHom_def F G :=
    hom_ext (MonoidalCategory.tensorHom_def ((forget k).map F) ((forget k).map G))
  id_tensorHom_id A B := hom_ext (MonoidalCategory.id_tensorHom_id A.toSCat B.toSCat)
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ :=
    hom_ext (MonoidalCategory.tensorHom_comp_tensorHom ((forget k).map f₁) ((forget k).map f₂)
      ((forget k).map g₁) ((forget k).map g₂))
  whiskerLeft_id A B := hom_ext (MonoidalCategory.whiskerLeft_id A.toSCat B.toSCat)
  id_whiskerRight A B := hom_ext (MonoidalCategory.id_whiskerRight A.toSCat B.toSCat)
  associator_naturality f₁ f₂ f₃ :=
    hom_ext (MonoidalCategory.associator_naturality ((forget k).map f₁) ((forget k).map f₂)
      ((forget k).map f₃))
  leftUnitor_naturality f := hom_ext (MonoidalCategory.leftUnitor_naturality ((forget k).map f))
  rightUnitor_naturality f := hom_ext (MonoidalCategory.rightUnitor_naturality ((forget k).map f))
  pentagon W X Y Z := hom_ext (MonoidalCategory.pentagon W.toSCat X.toSCat Y.toSCat Z.toSCat)
  triangle X Y := hom_ext (MonoidalCategory.triangle X.toSCat Y.toSCat)

end GSCat

end StringDiagrams

end
