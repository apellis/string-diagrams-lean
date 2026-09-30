import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax

/-!
# Conjugation by a family of adjoint equivalences

Let `B` be a bicategory, `X : B → B` a function on objects and `E x : X x ≌ x` a family of
adjoint equivalences (`e_x := (E x).hom`, `e'_x := (E x).inv`). Conjugation
`k ↦ e_x ≫ k ≫ e'_y` is a pseudofunctor `B ⥤ᵖ B` (`ConjPseudofunctor.pseudofunctor`) whose
composition constraint `(e_x ≫ k ≫ e'_y) ≫ (e_y ≫ l ≫ e'_z) ≅ e_x ≫ (k ≫ l) ≫ e'_z`
contracts `e'_y ≫ e_y` by the counit and whose unit constraint `e_x ≫ 𝟙 ≫ e'_x ≅ 𝟙` is the
inverse of the unit.

The components `e_x` form an oplax transformation from the conjugation pseudofunctor to the
identity (`ConjPseudofunctor.counitTrans`, with the invertible naturality 2-morphisms
`(e_x ≫ k ≫ e'_y) ≫ e_y ≅ e_x ≫ k`), the components `e'_x` an oplax transformation in the
other direction (`ConjPseudofunctor.unitTrans`), and these are inverse to each other up to
invertible modifications (`ConjPseudofunctor.counitTransCompUnitTrans`,
`ConjPseudofunctor.unitTransCompCounitTrans`) whose components are the unit and counit of the
`E x`.

Further general constructions used for the bicategorical Whitehead theorem:

* `PseudofunctorCopy.copy`: a pseudofunctor with its 1-morphisms replaced by isomorphic ones,
  transporting oplax transformations (`transLeft`, `transRight`) and invertible modifications
  (`modLeftRight`, `modRightLeft`);
* `PseudofunctorLift.lift`: lifting pseudofunctor data along a pseudofunctor `𝔉` that is fully
  faithful on 2-morphisms;
* `OplaxTransLift.lift`, `OplaxTransLift.liftCompIso`: lifting oplax transformations and
  invertible modifications along such an `𝔉`.

These are used in `StringDiagrams.Super.TwoSuperequivalenceWhitehead` to construct a
quasi-inverse of a local 2-superequivalence.
-/

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u

namespace ConjPseudofunctor

variable {B : Type u} [Bicategory.{w, v} B] {X : B → B} (E : ∀ x, X x ≌ x)

/-- Conjugation on 1-morphisms: `k ↦ e_x ≫ k ≫ e'_y`. -/
abbrev map {x y : B} (k : x ⟶ y) : X x ⟶ X y := (E x).hom ≫ k ≫ (E y).inv

/-- Conjugation on 2-morphisms: `η ↦ e_x ◁ η ▷ e'_y`. -/
def map₂ {x y : B} {k k' : x ⟶ y} (η : k ⟶ k') : map E k ⟶ map E k' :=
  (E x).hom ◁ η ▷ (E y).inv

/-- `(e_x ≫ k ≫ e'_y) ≫ e_y ≅ e_x ≫ k`, contracting `e'_y ≫ e_y` by the counit. -/
def counitNat {x y : B} (k : x ⟶ y) : map E k ≫ (E y).hom ≅ (E x).hom ≫ k :=
  α_ _ _ _ ≪≫ whiskerLeftIso (E x).hom (α_ _ _ _ ≪≫ whiskerLeftIso k (E y).counit ≪≫ ρ_ k)

/-- The composition constraint `(e_x ≫ k ≫ e'_y) ≫ (e_y ≫ l ≫ e'_z) ≅ e_x ≫ (k ≫ l) ≫ e'_z`. -/
def comp {x y z : B} (k : x ⟶ y) (l : y ⟶ z) : map E k ≫ map E l ≅ map E (k ≫ l) :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso (counitNat E k) (l ≫ (E z).inv) ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso (E x).hom (α_ k l (E z).inv).symm

/-- The unit constraint `e_x ≫ 𝟙 ≫ e'_x ≅ 𝟙`. -/
def id (x : B) : map E (𝟙 x) ≅ 𝟙 (X x) :=
  whiskerLeftIso (E x).hom (λ_ (E x).inv) ≪≫ (E x).unit.symm

theorem counitNat_hom {x y : B} (k : x ⟶ y) :
    (counitNat E k).hom = 𝟙 _ ⊗≫ (E x).hom ◁ k ◁ (E y).counit.hom ⊗≫ 𝟙 _ := by
  simp [counitNat]; bicategory

theorem comp_hom {x y z : B} (k : x ⟶ y) (l : y ⟶ z) :
    (comp E k l).hom = 𝟙 _ ⊗≫ (E x).hom ◁ k ◁ (E y).counit.hom ▷ l ▷ (E z).inv ⊗≫ 𝟙 _ := by
  simp [comp, counitNat]; bicategory

theorem comp_inv {x y z : B} (k : x ⟶ y) (l : y ⟶ z) :
    (comp E k l).inv = 𝟙 _ ⊗≫ (E x).hom ◁ k ◁ (E y).counit.inv ▷ l ▷ (E z).inv ⊗≫ 𝟙 _ := by
  simp [comp, counitNat]; bicategory

theorem id_hom (x : B) :
    (id E x).hom = 𝟙 _ ⊗≫ (E x).unit.inv := by
  simp [id]; bicategory

/-! ### The triangle identities in whiskered form -/

section Triangle

variable {a b : B} (e : a ≌ b)

theorem whiskerLeft_counit :
    e.hom ◁ e.counit.hom = 𝟙 _ ⊗≫ e.unit.inv ▷ e.hom ⊗≫ 𝟙 _ := by
  calc
    _ = 𝟙 _ ⊗≫ (e.unit.inv ▷ e.hom ≫ e.unit.hom ▷ e.hom) ⊗≫ e.hom ◁ e.counit.hom := by
      rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]; bicategory
    _ = 𝟙 _ ⊗≫ e.unit.inv ▷ e.hom ⊗≫ leftZigzag e.unit.hom e.counit.hom := by bicategory
    _ = _ := by rw [e.left_triangle_hom]; bicategory

theorem counit_whiskerRight :
    e.counit.hom ▷ e.inv = 𝟙 _ ⊗≫ e.inv ◁ e.unit.inv ⊗≫ 𝟙 _ := by
  calc
    _ = 𝟙 _ ⊗≫ (e.inv ◁ e.unit.inv ≫ e.inv ◁ e.unit.hom) ⊗≫ e.counit.hom ▷ e.inv := by
      rw [← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]; bicategory
    _ = 𝟙 _ ⊗≫ e.inv ◁ e.unit.inv ⊗≫ rightZigzag e.unit.hom e.counit.hom := by bicategory
    _ = _ := by rw [e.right_triangle_hom]; bicategory

theorem whiskerLeft_counit_inv :
    e.hom ◁ e.counit.inv = 𝟙 _ ⊗≫ e.unit.hom ▷ e.hom ⊗≫ 𝟙 _ := by
  calc
    _ = e.hom ◁ e.counit.inv ⊗≫ (e.unit.inv ▷ e.hom ≫ e.unit.hom ▷ e.hom) ⊗≫ 𝟙 _ := by
      rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]; bicategory
    _ = 𝟙 _ ⊗≫ rightZigzag e.counit.inv e.unit.inv ⊗≫ e.unit.hom ▷ e.hom ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      have := congrArg Iso.inv e.left_triangle
      simp only [leftZigzagIso_inv, Iso.trans_inv, Iso.symm_inv] at this
      rw [this]; bicategory

theorem counit_inv_whiskerRight :
    e.counit.inv ▷ e.inv = 𝟙 _ ⊗≫ e.inv ◁ e.unit.hom ⊗≫ 𝟙 _ := by
  calc
    _ = e.counit.inv ▷ e.inv ⊗≫ (e.inv ◁ e.unit.inv ≫ e.inv ◁ e.unit.hom) ⊗≫ 𝟙 _ := by
      rw [← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]; bicategory
    _ = 𝟙 _ ⊗≫ leftZigzag e.counit.inv e.unit.inv ⊗≫ e.inv ◁ e.unit.hom ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      have := congrArg Iso.inv e.right_triangle
      simp only [rightZigzagIso_inv, Iso.trans_inv, Iso.symm_inv] at this
      rw [this]; bicategory

end Triangle

/-! ### Naturality -/

@[simp] theorem map₂_id {x y : B} (k : x ⟶ y) : map₂ E (𝟙 k) = 𝟙 _ := by simp [map₂]

@[simp] theorem map₂_comp {x y : B} {k k' k'' : x ⟶ y} (η : k ⟶ k') (θ : k' ⟶ k'') :
    map₂ E (η ≫ θ) = map₂ E η ≫ map₂ E θ := by simp [map₂]

@[reassoc]
theorem counitNat_naturality {x y : B} {k k' : x ⟶ y} (η : k ⟶ k') :
    map₂ E η ▷ (E y).hom ≫ (counitNat E k').hom = (counitNat E k).hom ≫ (E x).hom ◁ η := by
  rw [counitNat_hom, counitNat_hom, map₂]
  calc
    _ = 𝟙 _ ⊗≫ (E x).hom ◁ (η ▷ ((E y).inv ≫ (E y).hom) ≫ k' ◁ (E y).counit.hom) ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by rw [← whisker_exchange]; bicategory

@[reassoc]
theorem comp_naturality_left {x y z : B} {k k' : x ⟶ y} (η : k ⟶ k') (l : y ⟶ z) :
    map₂ E η ▷ map E l ≫ (comp E k' l).hom = (comp E k l).hom ≫ map₂ E (η ▷ l) := by
  rw [comp_hom, comp_hom, map₂, map₂]
  calc
    _ = 𝟙 _ ⊗≫ (E x).hom ◁ (η ▷ ((E y).inv ≫ (E y).hom) ≫ k' ◁ (E y).counit.hom) ▷ l ▷
          (E z).inv ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by rw [← whisker_exchange]; bicategory

@[reassoc]
theorem comp_naturality_right {x y z : B} (k : x ⟶ y) {l l' : y ⟶ z} (η : l ⟶ l') :
    map E k ◁ map₂ E η ≫ (comp E k l').hom = (comp E k l).hom ≫ map₂ E (k ◁ η) := by
  rw [comp_hom, comp_hom, map₂, map₂]
  calc
    _ = 𝟙 _ ⊗≫ ((E x).hom ≫ k) ◁ (((E y).inv ≫ (E y).hom) ◁ η ▷ (E z).inv ≫
          (E y).counit.hom ▷ (l' ≫ (E z).inv)) ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by rw [whisker_exchange]; bicategory

/-! ### Coherence -/

theorem comp_associator {x y z t : B} (k : x ⟶ y) (l : y ⟶ z) (m : z ⟶ t) :
    (comp E k l).hom ▷ map E m ≫ (comp E (k ≫ l) m).hom ≫ map₂ E (α_ k l m).hom =
      (α_ _ _ _).hom ≫ map E k ◁ (comp E l m).hom ≫ (comp E k (l ≫ m)).hom := by
  rw [comp_hom, comp_hom, comp_hom, comp_hom, map₂]
  calc
    _ = 𝟙 _ ⊗≫ ((E x).hom ≫ k) ◁ ((E y).counit.hom ▷ (l ≫ ((E z).inv ≫ (E z).hom) ≫ m ≫
          (E t).inv) ≫ 𝟙 y ◁ l ◁ (E z).counit.hom ▷ (m ≫ (E t).inv)) ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by rw [← whisker_exchange]; bicategory

theorem comp_leftUnitor {x y : B} (k : x ⟶ y) :
    (comp E (𝟙 x) k).hom ≫ map₂ E (λ_ k).hom = (id E x).hom ▷ map E k ≫ (λ_ (map E k)).hom := by
  rw [comp_hom, id_hom, map₂]
  calc
    _ = 𝟙 _ ⊗≫ ((E x).hom ◁ (E x).counit.hom) ▷ (k ≫ (E y).inv) ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by rw [whiskerLeft_counit]; bicategory

theorem comp_rightUnitor {x y : B} (k : x ⟶ y) :
    (comp E k (𝟙 y)).hom ≫ map₂ E (ρ_ k).hom = map E k ◁ (id E y).hom ≫ (ρ_ (map E k)).hom := by
  rw [comp_hom, id_hom, map₂]
  calc
    _ = 𝟙 _ ⊗≫ ((E x).hom ≫ k) ◁ ((E y).counit.hom ▷ (E y).inv) ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by rw [counit_whiskerRight]; bicategory

/-! ### The conjugation pseudofunctor -/

/-- Conjugation by the adjoint equivalences `E x : X x ≌ x` as a pseudofunctor. -/
@[simps]
def pseudofunctor : Pseudofunctor B B where
  obj := X
  map := map E
  map₂ := map₂ E
  map₂_id := map₂_id E
  map₂_comp := map₂_comp E
  mapId := id E
  mapComp k l := (comp E k l).symm
  map₂_whisker_left k _ _ η := by
    simp only [Iso.symm_hom, Iso.symm_inv, Iso.eq_inv_comp, comp_naturality_right]
  map₂_whisker_right η l := by
    simp only [Iso.symm_hom, Iso.symm_inv, Iso.eq_inv_comp, comp_naturality_left]
  map₂_associator k l m := by
    simp only [Iso.symm_hom, Iso.symm_inv]
    rw [← comp_associator, inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc]
  map₂_left_unitor k := by
    simp only [Iso.symm_hom, Iso.eq_inv_comp, comp_leftUnitor]
  map₂_right_unitor k := by
    simp only [Iso.symm_hom, Iso.eq_inv_comp, comp_rightUnitor]

/-! ### The counit and unit transformations -/

/-- `k ≫ e'_y ≅ e'_x ≫ (e_x ≫ k ≫ e'_y)`, inserting `e'_x ≫ e_x` by the inverse counit. -/
def unitNat {x y : B} (k : x ⟶ y) : k ≫ (E y).inv ≅ (E x).inv ≫ map E k :=
  (λ_ _).symm ≪≫ whiskerRightIso (E x).counit.symm _ ≪≫ α_ _ _ _

theorem unitNat_hom {x y : B} (k : x ⟶ y) :
    (unitNat E k).hom = 𝟙 _ ⊗≫ (E x).counit.inv ▷ (k ≫ (E y).inv) ⊗≫ 𝟙 _ := by
  simp [unitNat]; bicategory

@[reassoc]
theorem unitNat_naturality {x y : B} {k k' : x ⟶ y} (η : k ⟶ k') :
    η ▷ (E y).inv ≫ (unitNat E k').hom = (unitNat E k).hom ≫ (E x).inv ◁ map₂ E η := by
  rw [unitNat_hom, unitNat_hom, map₂]
  calc
    _ = 𝟙 _ ⊗≫ (𝟙 x ◁ η ≫ (E x).counit.inv ▷ k') ▷ (E y).inv ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by rw [whisker_exchange]; bicategory

theorem counitNat_id (x : B) :
    (counitNat E (𝟙 x)).hom ≫ (E x).hom ◁ 𝟙 (𝟙 x) =
      (id E x).hom ▷ (E x).hom ≫ (λ_ (E x).hom).hom ≫ (ρ_ (E x).hom).inv := by
  rw [counitNat_hom, id_hom]
  calc
    _ = 𝟙 _ ⊗≫ (E x).hom ◁ (E x).counit.hom ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by rw [whiskerLeft_counit]; bicategory

theorem counitNat_comp {x y z : B} (k : x ⟶ y) (l : y ⟶ z) :
    (counitNat E (k ≫ l)).hom ≫ (E x).hom ◁ 𝟙 (k ≫ l) =
      (comp E k l).inv ▷ (E z).hom ≫ (α_ _ _ _).hom ≫ map E k ◁ (counitNat E l).hom ≫
        (α_ _ _ _).inv ≫ (counitNat E k).hom ▷ l ≫ (α_ _ _ _).hom := by
  simp only [counitNat_hom, comp_inv]
  symm
  calc
    _ = 𝟙 _ ⊗≫ ((E x).hom ≫ k) ◁ ((E y).counit.inv ▷ (l ≫ ((E z).inv ≫ (E z).hom)) ≫
          ((E y).inv ≫ (E y).hom) ◁ l ◁ (E z).counit.hom) ⊗≫
          ((E x).hom ≫ k) ◁ (E y).counit.hom ▷ l ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ ((E x).hom ≫ k) ◁ l ◁ (E z).counit.hom ⊗≫
          ((E x).hom ≫ k) ◁ ((E y).counit.inv ≫ (E y).counit.hom) ▷ l ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by rw [Iso.inv_hom_id]; bicategory

theorem unitNat_id (x : B) :
    (unitNat E (𝟙 x)).hom ≫ (E x).inv ◁ (id E x).hom =
      𝟙 (𝟙 x) ▷ (E x).inv ≫ (λ_ (E x).inv).hom ≫ (ρ_ (E x).inv).inv := by
  rw [unitNat_hom, id_hom]
  calc
    _ = 𝟙 _ ⊗≫ (E x).counit.inv ▷ (E x).inv ⊗≫ (E x).inv ◁ (E x).unit.inv ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (E x).inv ◁ ((E x).unit.hom ≫ (E x).unit.inv) ⊗≫ 𝟙 _ := by
      rw [counit_inv_whiskerRight]; bicategory
    _ = _ := by rw [Iso.hom_inv_id]; bicategory

theorem unitNat_comp {x y z : B} (k : x ⟶ y) (l : y ⟶ z) :
    (unitNat E (k ≫ l)).hom ≫ (E x).inv ◁ (comp E k l).inv =
      𝟙 (k ≫ l) ▷ (E z).inv ≫ (α_ _ _ _).hom ≫ k ◁ (unitNat E l).hom ≫
        (α_ _ _ _).inv ≫ (unitNat E k).hom ▷ map E l ≫ (α_ _ _ _).hom := by
  simp only [unitNat_hom, comp_inv]
  calc
    _ = 𝟙 _ ⊗≫ ((E x).counit.inv ▷ (k ≫ 𝟙 _ ≫ l ≫ (E z).inv) ≫
          ((E x).inv ≫ (E x).hom) ◁ k ◁ (E y).counit.inv ▷ (l ≫ (E z).inv)) ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by rw [← whisker_exchange]; bicategory

theorem counitNat_unitNat {x y : B} (k : x ⟶ y) :
    map E k ◁ (E y).unit.inv ≫ (ρ_ (map E k)).hom ≫ (λ_ (map E k)).inv =
      ((α_ _ _ _).inv ≫ (counitNat E k).hom ▷ (E y).inv ≫ (α_ _ _ _).hom ≫
        (E x).hom ◁ (unitNat E k).hom ≫ (α_ _ _ _).inv) ≫ (E x).unit.inv ▷ map E k := by
  simp only [counitNat_hom, unitNat_hom]
  symm
  calc
    _ = 𝟙 _ ⊗≫ ((E x).hom ≫ k) ◁ (E y).counit.hom ▷ (E y).inv ⊗≫
          ((E x).hom ◁ (E x).counit.inv) ▷ (k ≫ (E y).inv) ⊗≫
          (E x).unit.inv ▷ ((E x).hom ≫ k ≫ (E y).inv) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ ((E x).hom ≫ k) ◁ (E y).counit.hom ▷ (E y).inv ⊗≫
          ((E x).unit.hom ≫ (E x).unit.inv) ▷ ((E x).hom ≫ k ≫ (E y).inv) ⊗≫ 𝟙 _ := by
      rw [whiskerLeft_counit_inv]; bicategory
    _ = 𝟙 _ ⊗≫ ((E x).hom ≫ k) ◁ ((E y).counit.hom ▷ (E y).inv) ⊗≫ 𝟙 _ := by
      rw [Iso.hom_inv_id]; bicategory
    _ = _ := by rw [counit_whiskerRight]; bicategory

theorem unitNat_counitNat {x y : B} (k : x ⟶ y) :
    k ◁ (E y).counit.hom ≫ (ρ_ k).hom ≫ (λ_ k).inv =
      ((α_ _ _ _).inv ≫ (unitNat E k).hom ▷ (E y).hom ≫ (α_ _ _ _).hom ≫
        (E x).inv ◁ (counitNat E k).hom ≫ (α_ _ _ _).inv) ≫ (E x).counit.hom ▷ k := by
  simp only [counitNat_hom, unitNat_hom]
  symm
  calc
    _ = 𝟙 _ ⊗≫ ((E x).counit.inv ▷ (k ≫ (E y).inv ≫ (E y).hom) ≫
          ((E x).inv ≫ (E x).hom) ◁ k ◁ (E y).counit.hom) ⊗≫ (E x).counit.hom ▷ k ⊗≫
          𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ k ◁ (E y).counit.hom ⊗≫ ((E x).counit.inv ≫ (E x).counit.hom) ▷ k ⊗≫
          𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by rw [Iso.inv_hom_id]; bicategory

open Oplax in
/-- The oplax transformation from the conjugation pseudofunctor to the identity, with
components `e_x` and naturality 2-morphisms `(e_x ≫ k ≫ e'_y) ≫ e_y ≅ e_x ≫ k`. -/
@[simps]
def counitTrans : OplaxTrans (pseudofunctor E).toOplax (Pseudofunctor.id B).toOplax where
  app x := (E x).hom
  naturality k := (counitNat E k).hom
  naturality_naturality η := counitNat_naturality E η
  naturality_id x := counitNat_id E x
  naturality_comp k l := counitNat_comp E k l

open Oplax in
/-- The oplax transformation from the identity to the conjugation pseudofunctor, with
components `e'_x` and naturality 2-morphisms `k ≫ e'_y ≅ e'_x ≫ (e_x ≫ k ≫ e'_y)`. -/
@[simps]
def unitTrans : OplaxTrans (Pseudofunctor.id B).toOplax (pseudofunctor E).toOplax where
  app x := (E x).inv
  naturality k := (unitNat E k).hom
  naturality_naturality η := unitNat_naturality E η
  naturality_id x := unitNat_id E x
  naturality_comp k l := unitNat_comp E k l

open Oplax OplaxTrans in
/-- The composite of the counit and unit transformations is isomorphic to the identity of the
conjugation pseudofunctor, with components the inverse units `e_x ≫ e'_x ≅ 𝟙`. -/
def counitTransCompUnitTrans :
    counitTrans E ≫ unitTrans E ≅ 𝟙 (pseudofunctor E).toOplax :=
  OplaxTrans.isoMk (fun x => (E x).unit.symm) (fun {x y} k => by
    rw [categoryStruct_comp_naturality, categoryStruct_id_naturality]
    exact counitNat_unitNat E k)

open Oplax OplaxTrans in
/-- The composite of the unit and counit transformations is isomorphic to the identity of the
identity pseudofunctor, with components the counits `e'_x ≫ e_x ≅ 𝟙`. -/
def unitTransCompCounitTrans :
    unitTrans E ≫ counitTrans E ≅ 𝟙 (Pseudofunctor.id B).toOplax :=
  OplaxTrans.isoMk (fun x => (E x).counit) (fun {x y} k => by
    rw [categoryStruct_comp_naturality, categoryStruct_id_naturality]
    exact unitNat_counitNat E k)

end ConjPseudofunctor

/-! ## Replacing the 1-morphisms of a pseudofunctor by isomorphic ones -/

namespace PseudofunctorCopy

universe w₁ v₁ u₁ w₂ v₂ u₂

variable {𝒳 : Type u₁} [Bicategory.{w₁, v₁} 𝒳] {𝒴 : Type u₂} [Bicategory.{w₂, v₂} 𝒴]
  (Q : Pseudofunctor 𝒳 𝒴) (pmap : ∀ {a b : 𝒳}, (a ⟶ b) → (Q.obj a ⟶ Q.obj b))
  (κ : ∀ {a b : 𝒳} (f : a ⟶ b), pmap f ≅ Q.map f)

/-- `κ_f ⊗ κ_g : pmap f ≫ pmap g ≅ Q f ≫ Q g`. -/
def K2 {a b c : 𝒳} (f : a ⟶ b) (g : b ⟶ c) : pmap f ≫ pmap g ≅ Q.map f ≫ Q.map g :=
  whiskerRightIso (κ f) (pmap g) ≪≫ whiskerLeftIso (Q.map f) (κ g)

theorem K2_hom {a b c : 𝒳} (f : a ⟶ b) (g : b ⟶ c) :
    (K2 Q pmap κ f g).hom = (κ f).hom ▷ pmap g ≫ Q.map f ◁ (κ g).hom := rfl

theorem K2_inv {a b c : 𝒳} (f : a ⟶ b) (g : b ⟶ c) :
    (K2 Q pmap κ f g).inv = Q.map f ◁ (κ g).inv ≫ (κ f).inv ▷ pmap g := rfl

@[reassoc]
theorem K2_whiskerLeft {a b c : 𝒳} (f : a ⟶ b) {g h : b ⟶ c} (X : Q.map g ⟶ Q.map h) :
    (K2 Q pmap κ f g).inv ≫ pmap f ◁ ((κ g).hom ≫ X ≫ (κ h).inv) ≫ (K2 Q pmap κ f h).hom =
      Q.map f ◁ X := by
  rw [K2_inv, K2_hom]
  calc
    _ = 𝟙 _ ⊗≫ Q.map f ◁ (κ g).inv ⊗≫
          ((κ f).inv ▷ pmap g ≫ pmap f ◁ ((κ g).hom ≫ X ≫ (κ h).inv)) ⊗≫
          (κ f).hom ▷ pmap h ⊗≫ Q.map f ◁ (κ h).hom ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ Q.map f ◁ (κ g).inv ⊗≫ Q.map f ◁ ((κ g).hom ≫ X ≫ (κ h).inv) ⊗≫
          ((κ f).inv ≫ (κ f).hom) ▷ pmap h ⊗≫ Q.map f ◁ (κ h).hom ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ Q.map f ◁ ((κ g).inv ≫ (κ g).hom) ⊗≫ Q.map f ◁ X ⊗≫
          Q.map f ◁ ((κ h).inv ≫ (κ h).hom) ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id]; bicategory
    _ = _ := by rw [Iso.inv_hom_id, Iso.inv_hom_id]; bicategory

@[reassoc]
theorem K2_whiskerRight {a b c : 𝒳} {f g : a ⟶ b} (h : b ⟶ c) (X : Q.map f ⟶ Q.map g) :
    (K2 Q pmap κ f h).inv ≫ ((κ f).hom ≫ X ≫ (κ g).inv) ▷ pmap h ≫ (K2 Q pmap κ g h).hom =
      X ▷ Q.map h := by
  rw [K2_inv, K2_hom]
  calc
    _ = 𝟙 _ ⊗≫ (Q.map f ◁ (κ h).inv ≫
          ((κ f).inv ≫ (κ f).hom ≫ X ≫ (κ g).inv ≫ (κ g).hom) ▷ pmap h) ⊗≫
          Q.map g ◁ (κ h).hom ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ ((κ f).inv ≫ (κ f).hom) ▷ Q.map h ⊗≫ X ▷ Q.map h ⊗≫
          ((κ g).inv ≫ (κ g).hom) ▷ Q.map h ⊗≫ Q.map g ◁ ((κ h).inv ≫ (κ h).hom) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; bicategory
    _ = _ := by rw [Iso.inv_hom_id, Iso.inv_hom_id, Iso.inv_hom_id]; bicategory

@[reassoc]
theorem K2_assoc {a b c d : 𝒳} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (Q.map f ≫ Q.map g) ◁ (κ h).inv ≫ (K2 Q pmap κ f g).inv ▷ pmap h ≫ (α_ _ _ _).hom ≫
      (κ f).hom ▷ (pmap g ≫ pmap h) ≫ Q.map f ◁ (K2 Q pmap κ g h).hom = (α_ _ _ _).hom := by
  rw [K2_inv, K2_hom]
  calc
    _ = 𝟙 _ ⊗≫ (Q.map f ≫ Q.map g) ◁ (κ h).inv ⊗≫ Q.map f ◁ (κ g).inv ▷ pmap h ⊗≫
          ((κ f).inv ≫ (κ f).hom) ▷ (pmap g ≫ pmap h) ⊗≫ Q.map f ◁ (κ g).hom ▷ pmap h ⊗≫
          Q.map f ◁ Q.map g ◁ (κ h).hom ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (Q.map f ≫ Q.map g) ◁ (κ h).inv ⊗≫ Q.map f ◁ ((κ g).inv ≫ (κ g).hom) ▷ pmap h ⊗≫
          Q.map f ◁ Q.map g ◁ (κ h).hom ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id]; bicategory
    _ = 𝟙 _ ⊗≫ (Q.map f ≫ Q.map g) ◁ ((κ h).inv ≫ (κ h).hom) ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id]; bicategory
    _ = _ := by rw [Iso.inv_hom_id]; bicategory

@[reassoc]
theorem K2_comp_left {a b c d : 𝒳} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (K2 Q pmap κ (f ≫ g) h).inv ≫
        ((κ (f ≫ g)).hom ≫ (Q.mapComp f g).hom ≫ (K2 Q pmap κ f g).inv) ▷ pmap h =
      (Q.mapComp f g).hom ▷ Q.map h ≫ (Q.map f ≫ Q.map g) ◁ (κ h).inv ≫
        (K2 Q pmap κ f g).inv ▷ pmap h := by
  rw [K2_inv Q pmap κ (f ≫ g) h]
  simp only [Category.assoc, comp_whiskerRight, inv_hom_whiskerRight_assoc]
  rw [whisker_exchange_assoc]

@[reassoc]
theorem K2_comp_right {a b c d : 𝒳} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    pmap f ◁ ((K2 Q pmap κ g h).hom ≫ (Q.mapComp g h).inv ≫ (κ (g ≫ h)).inv) ≫
        (K2 Q pmap κ f (g ≫ h)).hom =
      (κ f).hom ▷ (pmap g ≫ pmap h) ≫ Q.map f ◁ (K2 Q pmap κ g h).hom ≫
        Q.map f ◁ (Q.mapComp g h).inv := by
  rw [K2_hom Q pmap κ f (g ≫ h), whisker_exchange_assoc]
  simp only [← whiskerLeft_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The pseudofunctor with the same objects as `Q`, 1-morphisms `pmap f` and all structure
transported along the isomorphisms `κ_f : pmap f ≅ Q f`. -/
@[simps]
def copy : Pseudofunctor 𝒳 𝒴 where
  obj := Q.obj
  map := pmap
  map₂ η := (κ _).hom ≫ Q.map₂ η ≫ (κ _).inv
  map₂_id f := by simp
  map₂_comp η θ := by simp
  mapId a := κ (𝟙 a) ≪≫ Q.mapId a
  mapComp f g := κ (f ≫ g) ≪≫ Q.mapComp f g ≪≫ (K2 Q pmap κ f g).symm
  map₂_whisker_left f g h η := by
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
      Pseudofunctor.map₂_whisker_left]
    rw [K2_whiskerLeft_assoc]
  map₂_whisker_right η h := by
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
      Pseudofunctor.map₂_whisker_right]
    rw [K2_whiskerRight_assoc]
  map₂_associator f g h := by
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
      Pseudofunctor.map₂_associator]
    rw [K2_comp_left_assoc, K2_comp_right_assoc, K2_assoc_assoc]
  map₂_left_unitor f := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Pseudofunctor.map₂_left_unitor, K2_inv, comp_whiskerRight, inv_hom_whiskerRight_assoc]
    rw [whisker_exchange_assoc, leftUnitor_naturality]
  map₂_right_unitor f := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Pseudofunctor.map₂_right_unitor, K2_inv]
    rw [whisker_exchange_assoc]
    simp only [← whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc]
    rw [← whisker_exchange_assoc, rightUnitor_naturality]

theorem copy_mapComp_inv {a b c : 𝒳} (f : a ⟶ b) (g : b ⟶ c) :
    ((copy Q pmap κ).mapComp f g).inv =
      (κ f).hom ▷ pmap g ≫ Q.map f ◁ (κ g).hom ≫ (Q.mapComp f g).inv ≫ (κ (f ≫ g)).inv := by
  simp only [copy_mapComp, Iso.trans_inv, Iso.symm_inv, K2_hom, Category.assoc]
  rfl

theorem copy_mapId_inv (a : 𝒳) :
    ((copy Q pmap κ).mapId a).inv = (Q.mapId a).inv ≫ (κ (𝟙 a)).inv :=
  rfl

/-! ### Transporting oplax transformations and modifications -/

open Oplax OplaxTrans

variable {H : OplaxFunctor 𝒳 𝒴}

omit [Bicategory 𝒳] in
theorem transLeft_aux {A B C A' B' C' : 𝒴} {qf pf : A ⟶ B} {qg pg : B ⟶ C} (kf : pf ≅ qf)
    (kg : pg ≅ qg) {sa : A ⟶ A'} {sb : B ⟶ B'} {sc : C ⟶ C'} {hf : A' ⟶ B'} {hg : B' ⟶ C'}
    (nf : qf ≫ sb ⟶ sa ≫ hf) (ng : qg ≫ sc ⟶ sb ≫ hg) :
    (qf ◁ kg.inv ≫ kf.inv ▷ pg) ▷ sc ≫ (α_ _ _ _).hom ≫ pf ◁ (kg.hom ▷ sc ≫ ng) ≫
        (α_ _ _ _).inv ≫ (kf.hom ▷ sb ≫ nf) ▷ hg ≫ (α_ _ _ _).hom =
      (α_ _ _ _).hom ≫ qf ◁ ng ≫ (α_ _ _ _).inv ≫ nf ▷ hg ≫ (α_ _ _ _).hom := by
  calc
    _ = 𝟙 _ ⊗≫ qf ◁ kg.inv ▷ sc ⊗≫ (kf.inv ▷ (pg ≫ sc) ≫ pf ◁ (kg.hom ▷ sc ≫ ng)) ⊗≫
          kf.hom ▷ sb ▷ hg ⊗≫ nf ▷ hg ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ qf ◁ (kg.inv ≫ kg.hom) ▷ sc ⊗≫ qf ◁ ng ⊗≫ (kf.inv ≫ kf.hom) ▷ (sb ≫ hg) ⊗≫
          nf ▷ hg ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by rw [Iso.inv_hom_id, Iso.inv_hom_id]; bicategory

omit [Bicategory 𝒳] in
theorem transRight_aux {A B C A' B' C' : 𝒴} {qf pf : A' ⟶ B'} {qg pg : B' ⟶ C'}
    (kf : pf ≅ qf) (kg : pg ≅ qg) {ta : A ⟶ A'} {tb : B ⟶ B'} {tc : C ⟶ C'} {hf : A ⟶ B}
    {hg : B ⟶ C} (nf : hf ≫ tb ⟶ ta ≫ qf) (ng : hg ≫ tc ⟶ tb ≫ qg) :
    (α_ _ _ _).hom ≫ hf ◁ ng ≫ (α_ _ _ _).inv ≫ nf ▷ qg ≫ (α_ _ _ _).hom ≫
        ta ◁ (qf ◁ kg.inv ≫ kf.inv ▷ pg) =
      (α_ _ _ _).hom ≫ hf ◁ (ng ≫ tb ◁ kg.inv) ≫ (α_ _ _ _).inv ≫ (nf ≫ ta ◁ kf.inv) ▷ pg ≫
        (α_ _ _ _).hom := by
  calc
    _ = 𝟙 _ ⊗≫ hf ◁ ng ⊗≫ (nf ▷ qg ≫ (ta ≫ qf) ◁ kg.inv) ⊗≫ ta ◁ kf.inv ▷ pg ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by rw [← whisker_exchange]; bicategory

/-- An oplax transformation out of `Q` gives one out of `copy Q pmap κ`, with the same
components and naturality 2-morphisms precomposed with `κ`. -/
@[simps]
def transLeft (σ : OplaxTrans Q.toOplax H) : OplaxTrans (copy Q pmap κ).toOplax H where
  app := σ.app
  naturality f := (κ f).hom ▷ σ.app _ ≫ σ.naturality f
  naturality_naturality {a b f g} η := by
    change ((κ f).hom ≫ Q.map₂ η ≫ (κ g).inv) ▷ σ.app b ≫ (κ g).hom ▷ σ.app b ≫
      σ.naturality g = ((κ f).hom ▷ σ.app b ≫ σ.naturality f) ≫ σ.app a ◁ H.map₂ η
    have h : Q.map₂ η ▷ σ.app b ≫ σ.naturality g = σ.naturality f ≫ σ.app a ◁ H.map₂ η :=
      σ.naturality_naturality η
    simp only [comp_whiskerRight, Category.assoc, inv_hom_whiskerRight_assoc, h]
  naturality_id a := by
    change ((κ (𝟙 a)).hom ▷ σ.app a ≫ σ.naturality (𝟙 a)) ≫ σ.app a ◁ H.mapId a =
      ((κ (𝟙 a)).hom ≫ (Q.mapId a).hom) ▷ σ.app a ≫ (λ_ (σ.app a)).hom ≫ (ρ_ (σ.app a)).inv
    have h : σ.naturality (𝟙 a) ≫ σ.app a ◁ H.mapId a =
        (Q.mapId a).hom ▷ σ.app a ≫ (λ_ (σ.app a)).hom ≫ (ρ_ (σ.app a)).inv :=
      σ.naturality_id a
    rw [Category.assoc, h, comp_whiskerRight, Category.assoc]
  naturality_comp {a b c} f g := by
    change ((κ (f ≫ g)).hom ▷ σ.app c ≫ σ.naturality (f ≫ g)) ≫ σ.app a ◁ H.mapComp f g =
      ((κ (f ≫ g)).hom ≫ (Q.mapComp f g).hom ≫ (K2 Q pmap κ f g).inv) ▷ σ.app c ≫
        (α_ _ _ _).hom ≫ pmap f ◁ ((κ g).hom ▷ σ.app c ≫ σ.naturality g) ≫ (α_ _ _ _).inv ≫
          ((κ f).hom ▷ σ.app b ≫ σ.naturality f) ▷ H.map g ≫ (α_ _ _ _).hom
    have h : σ.naturality (f ≫ g) ≫ σ.app a ◁ H.mapComp f g =
        (Q.mapComp f g).hom ▷ σ.app c ≫ (α_ _ _ _).hom ≫ Q.map f ◁ σ.naturality g ≫
          (α_ _ _ _).inv ≫ σ.naturality f ▷ H.map g ≫ (α_ _ _ _).hom :=
      σ.naturality_comp f g
    rw [Category.assoc, h, comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
      K2_inv, transLeft_aux]

/-- An oplax transformation into `Q` gives one into `copy Q pmap κ`, with the same components
and naturality 2-morphisms postcomposed with `κ⁻¹`. -/
@[simps]
def transRight (τ : OplaxTrans H Q.toOplax) : OplaxTrans H (copy Q pmap κ).toOplax where
  app := τ.app
  naturality f := τ.naturality f ≫ τ.app _ ◁ (κ f).inv
  naturality_naturality {a b f g} η := by
    change H.map₂ η ▷ τ.app b ≫ τ.naturality g ≫ τ.app a ◁ (κ g).inv =
      (τ.naturality f ≫ τ.app a ◁ (κ f).inv) ≫ τ.app a ◁ ((κ f).hom ≫ Q.map₂ η ≫ (κ g).inv)
    have h : H.map₂ η ▷ τ.app b ≫ τ.naturality g = τ.naturality f ≫ τ.app a ◁ Q.map₂ η :=
      τ.naturality_naturality η
    simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_inv_hom_assoc, reassoc_of% h]
  naturality_id a := by
    change (τ.naturality (𝟙 a) ≫ τ.app a ◁ (κ (𝟙 a)).inv) ≫
        τ.app a ◁ ((κ (𝟙 a)).hom ≫ (Q.mapId a).hom) =
      H.mapId a ▷ τ.app a ≫ (λ_ (τ.app a)).hom ≫ (ρ_ (τ.app a)).inv
    have h : τ.naturality (𝟙 a) ≫ τ.app a ◁ (Q.mapId a).hom =
        H.mapId a ▷ τ.app a ≫ (λ_ (τ.app a)).hom ≫ (ρ_ (τ.app a)).inv :=
      τ.naturality_id a
    simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_inv_hom_assoc, h]
  naturality_comp {a b c} f g := by
    change (τ.naturality (f ≫ g) ≫ τ.app a ◁ (κ (f ≫ g)).inv) ≫
        τ.app a ◁ ((κ (f ≫ g)).hom ≫ (Q.mapComp f g).hom ≫ (K2 Q pmap κ f g).inv) =
      H.mapComp f g ▷ τ.app c ≫ (α_ _ _ _).hom ≫ H.map f ◁ (τ.naturality g ≫ τ.app b ◁ (κ g).inv) ≫
        (α_ _ _ _).inv ≫ (τ.naturality f ≫ τ.app a ◁ (κ f).inv) ▷ pmap g ≫ (α_ _ _ _).hom
    have h : τ.naturality (f ≫ g) ≫ τ.app a ◁ (Q.mapComp f g).hom =
        H.mapComp f g ▷ τ.app c ≫ (α_ _ _ _).hom ≫ H.map f ◁ τ.naturality g ≫
          (α_ _ _ _).inv ≫ τ.naturality f ▷ Q.map g ≫ (α_ _ _ _).hom :=
      τ.naturality_comp f g
    rw [Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id_assoc, whiskerLeft_comp,
      reassoc_of% h, K2_inv]
    exact congrArg (H.mapComp f g ▷ τ.app c ≫ ·) (transRight_aux (κ f) (κ g) _ _)

omit [Bicategory 𝒳] in
theorem modLeftRight_aux {A B M N : 𝒴} {qf pf : A ⟶ B} (k : pf ≅ qf) {sa : A ⟶ M}
    {sb : B ⟶ N} {ta : M ⟶ A} {tb : N ⟶ B} {hf : M ⟶ N} (nσ : qf ≫ sb ⟶ sa ≫ hf)
    (nτ : hf ≫ tb ⟶ ta ≫ qf) (Γa : sa ≫ ta ⟶ 𝟙 A) (Γb : sb ≫ tb ⟶ 𝟙 B)
    (hΓ : qf ◁ Γb ≫ (ρ_ qf).hom ≫ (λ_ qf).inv =
      ((α_ _ _ _).inv ≫ nσ ▷ tb ≫ (α_ _ _ _).hom ≫ sa ◁ nτ ≫ (α_ _ _ _).inv) ≫ Γa ▷ qf) :
    pf ◁ Γb ≫ (ρ_ pf).hom ≫ (λ_ pf).inv =
      ((α_ _ _ _).inv ≫ (k.hom ▷ sb ≫ nσ) ▷ tb ≫ (α_ _ _ _).hom ≫ sa ◁ (nτ ≫ ta ◁ k.inv) ≫
        (α_ _ _ _).inv) ≫ Γa ▷ pf := by
  symm
  calc
    _ = 𝟙 _ ⊗≫ k.hom ▷ (sb ≫ tb) ⊗≫ nσ ▷ tb ⊗≫ sa ◁ nτ ⊗≫ ((sa ≫ ta) ◁ k.inv ≫ Γa ▷ pf) ⊗≫
          𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ k.hom ▷ (sb ≫ tb) ⊗≫
          (((α_ _ _ _).inv ≫ nσ ▷ tb ≫ (α_ _ _ _).hom ≫ sa ◁ nτ ≫ (α_ _ _ _).inv) ≫ Γa ▷ qf) ⊗≫
          𝟙 A ◁ k.inv ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ (k.hom ▷ (sb ≫ tb) ≫ qf ◁ Γb) ⊗≫ 𝟙 A ◁ k.inv ⊗≫ 𝟙 _ := by
      rw [← hΓ]; bicategory
    _ = 𝟙 _ ⊗≫ pf ◁ Γb ⊗≫ (k.hom ≫ k.inv) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by rw [Iso.hom_inv_id]; bicategory

omit [Bicategory 𝒳] in
theorem modRightLeft_aux {A B M N : 𝒴} {qf pf : A ⟶ B} (k : pf ≅ qf) {sa : A ⟶ M}
    {sb : B ⟶ N} {ta : M ⟶ A} {tb : N ⟶ B} {hf : M ⟶ N} (nσ : qf ≫ sb ⟶ sa ≫ hf)
    (nτ : hf ≫ tb ⟶ ta ≫ qf) :
    (α_ _ _ _).inv ≫ (nτ ≫ ta ◁ k.inv) ▷ sb ≫ (α_ _ _ _).hom ≫ ta ◁ (k.hom ▷ sb ≫ nσ) ≫
        (α_ _ _ _).inv =
      (α_ _ _ _).inv ≫ nτ ▷ sb ≫ (α_ _ _ _).hom ≫ ta ◁ nσ ≫ (α_ _ _ _).inv := by
  calc
    _ = 𝟙 _ ⊗≫ nτ ▷ sb ⊗≫ ta ◁ (k.inv ≫ k.hom) ▷ sb ⊗≫ ta ◁ nσ ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by rw [Iso.inv_hom_id]; bicategory

/-- The components of an isomorphism of oplax transformations. -/
@[simps]
def appIso {F G : OplaxFunctor 𝒳 𝒴} {η θ : F ⟶ G} (Γ : η ≅ θ) (a : 𝒳) :
    η.app a ≅ θ.app a where
  hom := Γ.hom.as.app a
  inv := Γ.inv.as.app a
  hom_inv_id := congrArg (fun m => m.as.app a) Γ.hom_inv_id
  inv_hom_id := congrArg (fun m => m.as.app a) Γ.inv_hom_id

/-- An isomorphism `σ ≫ τ ≅ 𝟙` transported to the copies. -/
def modLeftRight (σ : OplaxTrans Q.toOplax H) (τ : OplaxTrans H Q.toOplax)
    (Γ : σ ≫ τ ≅ 𝟙 Q.toOplax) :
    transLeft Q pmap κ σ ≫ transRight Q pmap κ τ ≅ 𝟙 (copy Q pmap κ).toOplax :=
  OplaxTrans.isoMk (fun a => appIso Γ a) (fun {a b} f => by
    have h : Q.map f ◁ Γ.hom.as.app b ≫ (ρ_ (Q.map f)).hom ≫ (λ_ (Q.map f)).inv =
        ((α_ _ _ _).inv ≫ σ.naturality f ▷ τ.app b ≫ (α_ _ _ _).hom ≫
          σ.app a ◁ τ.naturality f ≫ (α_ _ _ _).inv) ≫ Γ.hom.as.app a ▷ Q.map f :=
      Γ.hom.as.naturality f
    exact modLeftRight_aux (κ f) (σ.naturality f) (τ.naturality f) _ _ h)

/-- An isomorphism `τ ≫ σ ≅ 𝟙` transported to the copies. -/
def modRightLeft (σ : OplaxTrans Q.toOplax H) (τ : OplaxTrans H Q.toOplax)
    (Γ : τ ≫ σ ≅ 𝟙 H) :
    transRight Q pmap κ τ ≫ transLeft Q pmap κ σ ≅ 𝟙 H :=
  OplaxTrans.isoMk (fun a => appIso Γ a) (fun {a b} f => by
    have h : H.map f ◁ Γ.hom.as.app b ≫ (ρ_ (H.map f)).hom ≫ (λ_ (H.map f)).inv =
        ((α_ _ _ _).inv ≫ τ.naturality f ▷ σ.app b ≫ (α_ _ _ _).hom ≫
          τ.app a ◁ σ.naturality f ≫ (α_ _ _ _).inv) ≫ Γ.hom.as.app a ▷ H.map f :=
      Γ.hom.as.naturality f
    refine h.trans ?_
    exact congrArg (· ≫ Γ.hom.as.app a ▷ H.map f)
      (modRightLeft_aux (κ f) (σ.naturality f) (τ.naturality f)).symm)

end PseudofunctorCopy

/-! ## Lifting a pseudofunctor along a locally fully faithful pseudofunctor -/

namespace PseudofunctorLift

universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃

variable {𝔅 : Type u₁} [Bicategory.{w₁, v₁} 𝔅] {𝒞 : Type u₂} [Bicategory.{w₂, v₂} 𝒞]
  {𝒳 : Type u₃} [Bicategory.{w₃, v₃} 𝒳] (𝔉 : Pseudofunctor 𝔅 𝒞)
  (pre : ∀ {a b : 𝔅} {f g : a ⟶ b}, (𝔉.map f ⟶ 𝔉.map g) → (f ⟶ g))
  (map_pre : ∀ {a b : 𝔅} {f g : a ⟶ b} (x : 𝔉.map f ⟶ 𝔉.map g), 𝔉.map₂ (pre x) = x)
  (pre_map : ∀ {a b : 𝔅} {f g : a ⟶ b} (x : f ⟶ g), pre (𝔉.map₂ x) = x)
  (gobj : 𝒳 → 𝔅) (gmap : ∀ {x y : 𝒳}, (x ⟶ y) → (gobj x ⟶ gobj y))
  (map₂' : ∀ {x y : 𝒳} {f g : x ⟶ y}, (f ⟶ g) → (𝔉.map (gmap f) ⟶ 𝔉.map (gmap g)))
  (mapId' : ∀ x : 𝒳, 𝔉.map (gmap (𝟙 x)) ≅ 𝟙 (𝔉.obj (gobj x)))
  (mapComp' : ∀ {x y z : 𝒳} (f : x ⟶ y) (g : y ⟶ z),
    𝔉.map (gmap (f ≫ g)) ≅ 𝔉.map (gmap f) ≫ 𝔉.map (gmap g))

include pre_map in
theorem map₂_injective {a b : 𝔅} {f g : a ⟶ b} {x y : f ⟶ g} (h : 𝔉.map₂ x = 𝔉.map₂ y) :
    x = y := by
  rw [← pre_map x, ← pre_map y, h]

/-- The preimage of an isomorphism. -/
@[simps]
def preIso {a b : 𝔅} {f g : a ⟶ b} (e : 𝔉.map f ≅ 𝔉.map g) : f ≅ g where
  hom := pre e.hom
  inv := pre e.inv
  hom_inv_id := map₂_injective 𝔉 pre pre_map (by simp [map_pre])
  inv_hom_id := map₂_injective 𝔉 pre pre_map (by simp [map_pre])

/-- Given pseudofunctor data on the 1-morphisms `𝔉 (gmap f)`, the lift of this pseudofunctor
along `𝔉` (which is fully faithful on 2-morphisms). -/
@[simps]
def lift
    (map₂_id' : ∀ {x y : 𝒳} (f : x ⟶ y), map₂' (𝟙 f) = 𝟙 _)
    (map₂_comp' : ∀ {x y : 𝒳} {f g h : x ⟶ y} (η : f ⟶ g) (θ : g ⟶ h),
      map₂' (η ≫ θ) = map₂' η ≫ map₂' θ)
    (map₂_whisker_left' : ∀ {x y z : 𝒳} (f : x ⟶ y) {g h : y ⟶ z} (η : g ⟶ h),
      map₂' (f ◁ η) = (mapComp' f g).hom ≫ 𝔉.map (gmap f) ◁ map₂' η ≫ (mapComp' f h).inv)
    (map₂_whisker_right' : ∀ {x y z : 𝒳} {f g : x ⟶ y} (η : f ⟶ g) (h : y ⟶ z),
      map₂' (η ▷ h) = (mapComp' f h).hom ≫ map₂' η ▷ 𝔉.map (gmap h) ≫ (mapComp' g h).inv)
    (map₂_associator' : ∀ {x y z t : 𝒳} (f : x ⟶ y) (g : y ⟶ z) (h : z ⟶ t),
      map₂' (α_ f g h).hom = (mapComp' (f ≫ g) h).hom ≫ (mapComp' f g).hom ▷ 𝔉.map (gmap h) ≫
        (α_ _ _ _).hom ≫ 𝔉.map (gmap f) ◁ (mapComp' g h).inv ≫ (mapComp' f (g ≫ h)).inv)
    (map₂_left_unitor' : ∀ {x y : 𝒳} (f : x ⟶ y),
      map₂' (λ_ f).hom = (mapComp' (𝟙 x) f).hom ≫ (mapId' x).hom ▷ 𝔉.map (gmap f) ≫
        (λ_ _).hom)
    (map₂_right_unitor' : ∀ {x y : 𝒳} (f : x ⟶ y),
      map₂' (ρ_ f).hom = (mapComp' f (𝟙 y)).hom ≫ 𝔉.map (gmap f) ◁ (mapId' y).hom ≫
        (ρ_ _).hom) :
    Pseudofunctor 𝒳 𝔅 where
  obj := gobj
  map := gmap
  map₂ η := pre (map₂' η)
  map₂_id f := map₂_injective 𝔉 pre pre_map (by simp [map_pre, map₂_id'])
  map₂_comp η θ := map₂_injective 𝔉 pre pre_map (by simp [map_pre, map₂_comp'])
  mapId x := preIso 𝔉 pre map_pre pre_map (mapId' x ≪≫ (𝔉.mapId _).symm)
  mapComp f g := preIso 𝔉 pre map_pre pre_map (mapComp' f g ≪≫ (𝔉.mapComp _ _).symm)
  map₂_whisker_left f g h η := map₂_injective 𝔉 pre pre_map (by
    simp [map_pre, map₂_whisker_left'])
  map₂_whisker_right η h := map₂_injective 𝔉 pre pre_map (by
    simp [map_pre, map₂_whisker_right'])
  map₂_associator f g h := map₂_injective 𝔉 pre pre_map (by
    simp [map_pre, map₂_associator'])
  map₂_left_unitor f := map₂_injective 𝔉 pre pre_map (by
    simp [map_pre, map₂_left_unitor'])
  map₂_right_unitor f := map₂_injective 𝔉 pre pre_map (by
    simp [map_pre, map₂_right_unitor'])

section

variable (map₂_id' : ∀ {x y : 𝒳} (f : x ⟶ y), map₂' (𝟙 f) = 𝟙 _)
    (map₂_comp' : ∀ {x y : 𝒳} {f g h : x ⟶ y} (η : f ⟶ g) (θ : g ⟶ h),
      map₂' (η ≫ θ) = map₂' η ≫ map₂' θ)
    (map₂_whisker_left' : ∀ {x y z : 𝒳} (f : x ⟶ y) {g h : y ⟶ z} (η : g ⟶ h),
      map₂' (f ◁ η) = (mapComp' f g).hom ≫ 𝔉.map (gmap f) ◁ map₂' η ≫ (mapComp' f h).inv)
    (map₂_whisker_right' : ∀ {x y z : 𝒳} {f g : x ⟶ y} (η : f ⟶ g) (h : y ⟶ z),
      map₂' (η ▷ h) = (mapComp' f h).hom ≫ map₂' η ▷ 𝔉.map (gmap h) ≫ (mapComp' g h).inv)
    (map₂_associator' : ∀ {x y z t : 𝒳} (f : x ⟶ y) (g : y ⟶ z) (h : z ⟶ t),
      map₂' (α_ f g h).hom = (mapComp' (f ≫ g) h).hom ≫ (mapComp' f g).hom ▷ 𝔉.map (gmap h) ≫
        (α_ _ _ _).hom ≫ 𝔉.map (gmap f) ◁ (mapComp' g h).inv ≫ (mapComp' f (g ≫ h)).inv)
    (map₂_left_unitor' : ∀ {x y : 𝒳} (f : x ⟶ y),
      map₂' (λ_ f).hom = (mapComp' (𝟙 x) f).hom ≫ (mapId' x).hom ▷ 𝔉.map (gmap f) ≫
        (λ_ _).hom)
    (map₂_right_unitor' : ∀ {x y : 𝒳} (f : x ⟶ y),
      map₂' (ρ_ f).hom = (mapComp' f (𝟙 y)).hom ≫ 𝔉.map (gmap f) ◁ (mapId' y).hom ≫
        (ρ_ _).hom)

include map_pre in
theorem map₂_lift_mapComp_inv {x y z : 𝒳} (f : x ⟶ y) (g : y ⟶ z) :
    𝔉.map₂ ((lift 𝔉 pre map_pre pre_map gobj gmap map₂' mapId' mapComp' map₂_id' map₂_comp'
      map₂_whisker_left' map₂_whisker_right' map₂_associator' map₂_left_unitor'
      map₂_right_unitor').mapComp f g).inv =
        (𝔉.mapComp (gmap f) (gmap g)).hom ≫ (mapComp' f g).inv :=
  map_pre _

include map_pre in
theorem map₂_lift_mapComp_hom {x y z : 𝒳} (f : x ⟶ y) (g : y ⟶ z) :
    𝔉.map₂ ((lift 𝔉 pre map_pre pre_map gobj gmap map₂' mapId' mapComp' map₂_id' map₂_comp'
      map₂_whisker_left' map₂_whisker_right' map₂_associator' map₂_left_unitor'
      map₂_right_unitor').mapComp f g).hom =
        (mapComp' f g).hom ≫ (𝔉.mapComp (gmap f) (gmap g)).inv :=
  map_pre _

include map_pre in
theorem map₂_lift_mapId_hom (x : 𝒳) :
    𝔉.map₂ ((lift 𝔉 pre map_pre pre_map gobj gmap map₂' mapId' mapComp' map₂_id' map₂_comp'
      map₂_whisker_left' map₂_whisker_right' map₂_associator' map₂_left_unitor'
      map₂_right_unitor').mapId x).hom =
        (mapId' x).hom ≫ (𝔉.mapId (gobj x)).inv :=
  map_pre _

include map_pre in
theorem map₂_lift_mapId_inv (x : 𝒳) :
    𝔉.map₂ ((lift 𝔉 pre map_pre pre_map gobj gmap map₂' mapId' mapComp' map₂_id' map₂_comp'
      map₂_whisker_left' map₂_whisker_right' map₂_associator' map₂_left_unitor'
      map₂_right_unitor').mapId x).inv =
        (𝔉.mapId (gobj x)).hom ≫ (mapId' x).inv :=
  map_pre _

end

end PseudofunctorLift

/-! ## Lifting oplax transformations along a locally fully faithful pseudofunctor -/

namespace OplaxTransLift

universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃

open Oplax

variable {𝔅 : Type u₁} [Bicategory.{w₁, v₁} 𝔅] {𝒞 : Type u₂} [Bicategory.{w₂, v₂} 𝒞]
  {𝒳 : Type u₃} [Bicategory.{w₃, v₃} 𝒳] (𝔉 : Pseudofunctor 𝔅 𝒞)
  (pre : ∀ {a b : 𝔅} {f g : a ⟶ b}, (𝔉.map f ⟶ 𝔉.map g) → (f ⟶ g))
  (map_pre : ∀ {a b : 𝔅} {f g : a ⟶ b} (x : 𝔉.map f ⟶ 𝔉.map g), 𝔉.map₂ (pre x) = x)
  (pre_map : ∀ {a b : 𝔅} {f g : a ⟶ b} (x : f ⟶ g), pre (𝔉.map₂ x) = x)
  {S S' : OplaxFunctor 𝒳 𝔅}
  (σapp : ∀ a, 𝔉.obj (S.obj a) ⟶ 𝔉.obj (S'.obj a))
  (σnat : ∀ {a b : 𝒳} (f : a ⟶ b),
    𝔉.map (S.map f) ≫ σapp b ⟶ σapp a ≫ 𝔉.map (S'.map f))
  (t : ∀ a, S.obj a ⟶ S'.obj a) (κ : ∀ a, 𝔉.map (t a) ≅ σapp a)

omit [Bicategory 𝒳] in
theorem map₂_associator_inv {a b c d : 𝔅} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    𝔉.map₂ (α_ f g h).inv = (𝔉.mapComp f (g ≫ h)).hom ≫ 𝔉.map f ◁ (𝔉.mapComp g h).hom ≫
      (α_ _ _ _).inv ≫ (𝔉.mapComp f g).inv ▷ 𝔉.map h ≫ (𝔉.mapComp (f ≫ g) h).inv := by
  rw [𝔉.mapComp_assoc_right_hom_assoc]
  simp

/-- The naturality 2-morphisms of the lift, before taking preimages. -/
def natU {a b : 𝒳} (f : a ⟶ b) : 𝔉.map (S.map f ≫ t b) ⟶ 𝔉.map (t a ≫ S'.map f) :=
  (𝔉.mapComp (S.map f) (t b)).hom ≫ 𝔉.map (S.map f) ◁ (κ b).hom ≫ σnat f ≫
    (κ a).inv ▷ 𝔉.map (S'.map f) ≫ (𝔉.mapComp (t a) (S'.map f)).inv

include map_pre pre_map in
/-- The oplax transformation `S ⟶ S'` with components `t a` whose image under `𝔉` is the
oplax transformation `(σapp, σnat)` (up to the isomorphisms `κ`). -/
@[simps]
def lift
    (nat_nat : ∀ {a b : 𝒳} {f g : a ⟶ b} (β : f ⟶ g),
      𝔉.map₂ (S.map₂ β) ▷ σapp b ≫ σnat g = σnat f ≫ σapp a ◁ 𝔉.map₂ (S'.map₂ β))
    (nat_id : ∀ a : 𝒳, σnat (𝟙 a) ≫ σapp a ◁ (𝔉.map₂ (S'.mapId a) ≫ (𝔉.mapId _).hom) =
      (𝔉.map₂ (S.mapId a) ≫ (𝔉.mapId _).hom) ▷ σapp a ≫ (λ_ _).hom ≫ (ρ_ _).inv)
    (nat_comp : ∀ {a b c : 𝒳} (f : a ⟶ b) (g : b ⟶ c),
      σnat (f ≫ g) ≫ σapp a ◁ (𝔉.map₂ (S'.mapComp f g) ≫ (𝔉.mapComp _ _).hom) =
        (𝔉.map₂ (S.mapComp f g) ≫ (𝔉.mapComp _ _).hom) ▷ σapp c ≫ (α_ _ _ _).hom ≫
          𝔉.map (S.map f) ◁ σnat g ≫ (α_ _ _ _).inv ≫ σnat f ▷ 𝔉.map (S'.map g) ≫
            (α_ _ _ _).hom) :
    OplaxTrans S S' where
  app := t
  naturality f := pre (natU 𝔉 σapp σnat t κ f)
  naturality_naturality {a b f g} β := PseudofunctorLift.map₂_injective 𝔉 pre pre_map (by
    simp only [PrelaxFunctor.map₂_comp, map_pre, natU, Pseudofunctor.map₂_whisker_right,
      Pseudofunctor.map₂_whisker_left, Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← whisker_exchange_assoc, reassoc_of% (nat_nat β), whisker_exchange_assoc])
  naturality_id a := by
    rw [← cancel_mono (ρ_ (t a)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply PseudofunctorLift.map₂_injective 𝔉 pre pre_map
    simp only [PrelaxFunctor.map₂_comp, map_pre, natU, Pseudofunctor.map₂_whisker_right,
      Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_left_unitor,
      Pseudofunctor.map₂_right_unitor, Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    calc
      _ = 𝟙 _ ⊗≫ 𝔉.map (S.map (𝟙 a)) ◁ (κ a).hom ⊗≫ σnat (𝟙 a) ⊗≫
            ((κ a).inv ▷ 𝔉.map (S'.map (𝟙 a)) ≫
              𝔉.map (t a) ◁ (𝔉.map₂ (S'.mapId a) ≫ (𝔉.mapId _).hom)) ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ 𝔉.map (S.map (𝟙 a)) ◁ (κ a).hom ⊗≫
            (σnat (𝟙 a) ≫ σapp a ◁ (𝔉.map₂ (S'.mapId a) ≫ (𝔉.mapId _).hom)) ⊗≫
            (κ a).inv ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
      _ = 𝟙 _ ⊗≫ (𝔉.map (S.map (𝟙 a)) ◁ (κ a).hom ≫
            (𝔉.map₂ (S.mapId a) ≫ (𝔉.mapId _).hom) ▷ σapp a) ⊗≫ (κ a).inv ⊗≫ 𝟙 _ := by
        rw [nat_id a]; bicategory
      _ = 𝟙 _ ⊗≫ (𝔉.map₂ (S.mapId a) ≫ (𝔉.mapId _).hom) ▷ 𝔉.map (t a) ⊗≫
            ((κ a).hom ≫ (κ a).inv) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; bicategory
      _ = _ := by rw [Iso.hom_inv_id]; bicategory
  naturality_comp {a b c} f g := by
    apply PseudofunctorLift.map₂_injective 𝔉 pre pre_map
    simp only [PrelaxFunctor.map₂_comp, map_pre, natU, Pseudofunctor.map₂_whisker_right,
      Pseudofunctor.map₂_whisker_left, map₂_associator_inv, Pseudofunctor.map₂_associator,
      Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp, comp_whiskerRight,
      whiskerLeft_inv_hom_assoc, inv_hom_whiskerRight_assoc]
    congr 1
    symm
    calc
      _ = 𝟙 _ ⊗≫ (𝔉.map₂ (S.mapComp f g) ≫ (𝔉.mapComp (S.map f) (S.map g)).hom) ▷
              𝔉.map (t c) ⊗≫
            𝔉.map (S.map f) ◁ 𝔉.map (S.map g) ◁ (κ c).hom ⊗≫ 𝔉.map (S.map f) ◁ σnat g ⊗≫
            𝔉.map (S.map f) ◁ ((κ b).inv ≫ (κ b).hom) ▷ 𝔉.map (S'.map g) ⊗≫
            σnat f ▷ 𝔉.map (S'.map g) ⊗≫
            (κ a).inv ▷ (𝔉.map (S'.map f) ≫ 𝔉.map (S'.map g)) ⊗≫
            𝔉.map (t a) ◁ (𝔉.mapComp (S'.map f) (S'.map g)).inv ⊗≫
            (𝔉.mapComp (t a) (S'.map f ≫ S'.map g)).inv := by
        bicategory
      _ = 𝟙 _ ⊗≫ ((𝔉.map₂ (S.mapComp f g) ≫ (𝔉.mapComp (S.map f) (S.map g)).hom) ▷
              𝔉.map (t c) ≫ (𝔉.map (S.map f) ≫ 𝔉.map (S.map g)) ◁ (κ c).hom) ⊗≫
            𝔉.map (S.map f) ◁ σnat g ⊗≫ σnat f ▷ 𝔉.map (S'.map g) ⊗≫
            ((κ a).inv ▷ (𝔉.map (S'.map f) ≫ 𝔉.map (S'.map g)) ≫
              𝔉.map (t a) ◁ (𝔉.mapComp (S'.map f) (S'.map g)).inv) ⊗≫
            (𝔉.mapComp (t a) (S'.map f ≫ S'.map g)).inv := by
        rw [Iso.inv_hom_id]; bicategory
      _ = 𝟙 _ ⊗≫ (𝔉.map (S.map (f ≫ g)) ◁ (κ c).hom ≫
              (𝔉.map₂ (S.mapComp f g) ≫ (𝔉.mapComp (S.map f) (S.map g)).hom) ▷ σapp c) ⊗≫
            𝔉.map (S.map f) ◁ σnat g ⊗≫ σnat f ▷ 𝔉.map (S'.map g) ⊗≫
            (σapp a ◁ (𝔉.mapComp (S'.map f) (S'.map g)).inv ≫
              (κ a).inv ▷ 𝔉.map (S'.map f ≫ S'.map g)) ⊗≫
            (𝔉.mapComp (t a) (S'.map f ≫ S'.map g)).inv := by
        rw [← whisker_exchange, ← whisker_exchange]
      _ = 𝟙 _ ⊗≫ 𝔉.map (S.map (f ≫ g)) ◁ (κ c).hom ⊗≫
            ((𝔉.map₂ (S.mapComp f g) ≫ (𝔉.mapComp _ _).hom) ▷ σapp c ≫ (α_ _ _ _).hom ≫
              𝔉.map (S.map f) ◁ σnat g ≫ (α_ _ _ _).inv ≫ σnat f ▷ 𝔉.map (S'.map g) ≫
                (α_ _ _ _).hom) ⊗≫
            σapp a ◁ (𝔉.mapComp (S'.map f) (S'.map g)).inv ⊗≫
            (κ a).inv ▷ 𝔉.map (S'.map f ≫ S'.map g) ⊗≫
            (𝔉.mapComp (t a) (S'.map f ≫ S'.map g)).inv := by
        bicategory
      _ = 𝟙 _ ⊗≫ 𝔉.map (S.map (f ≫ g)) ◁ (κ c).hom ⊗≫ σnat (f ≫ g) ⊗≫
            σapp a ◁ 𝔉.map₂ (S'.mapComp f g) ⊗≫
            σapp a ◁ ((𝔉.mapComp (S'.map f) (S'.map g)).hom ≫
              (𝔉.mapComp (S'.map f) (S'.map g)).inv) ⊗≫
            (κ a).inv ▷ 𝔉.map (S'.map f ≫ S'.map g) ⊗≫
            (𝔉.mapComp (t a) (S'.map f ≫ S'.map g)).inv := by
        rw [← nat_comp]; bicategory
      _ = 𝟙 _ ⊗≫ 𝔉.map (S.map (f ≫ g)) ◁ (κ c).hom ⊗≫ σnat (f ≫ g) ⊗≫
            (σapp a ◁ 𝔉.map₂ (S'.mapComp f g) ≫ (κ a).inv ▷ 𝔉.map (S'.map f ≫ S'.map g)) ⊗≫
            (𝔉.mapComp (t a) (S'.map f ≫ S'.map g)).inv := by
        rw [Iso.hom_inv_id]; bicategory
      _ = _ := by rw [whisker_exchange]; bicategory

section Mod

variable (σ'app : ∀ a, 𝔉.obj (S'.obj a) ⟶ 𝔉.obj (S.obj a))
  (σ'nat : ∀ {a b : 𝒳} (f : a ⟶ b),
    𝔉.map (S'.map f) ≫ σ'app b ⟶ σ'app a ≫ 𝔉.map (S.map f))
  (t' : ∀ a, S'.obj a ⟶ S.obj a) (κ' : ∀ a, 𝔉.map (t' a) ≅ σ'app a)
  (Γ : ∀ a, σapp a ≫ σ'app a ≅ 𝟙 _)

/-- The components of the lifted modification `t ≫ t' ≅ 𝟙`. -/
def modApp (a : 𝒳) : 𝔉.map (t a ≫ t' a) ≅ 𝔉.map (𝟙 (S.obj a)) :=
  𝔉.mapComp (t a) (t' a) ≪≫ whiskerRightIso (κ a) _ ≪≫ whiskerLeftIso _ (κ' a) ≪≫ Γ a ≪≫
    (𝔉.mapId _).symm

omit [Bicategory 𝒳] in
theorem modApp_aux {A B M N : 𝒞} {sf : A ⟶ B} {sf' : M ⟶ N} {ta sa : A ⟶ M} {tb sb : B ⟶ N}
    {ta' sa' : M ⟶ A} {tb' sb' : N ⟶ B} (ka : ta ≅ sa) (kb : tb ≅ sb) (ka' : ta' ≅ sa')
    (kb' : tb' ≅ sb') (nσ : sf ≫ sb ⟶ sa ≫ sf') (nσ' : sf' ≫ sb' ⟶ sa' ≫ sf)
    (Γa : sa ≫ sa' ⟶ 𝟙 A) (Γb : sb ≫ sb' ⟶ 𝟙 B)
    (hΓ : sf ◁ Γb ≫ (ρ_ sf).hom ≫ (λ_ sf).inv =
      ((α_ _ _ _).inv ≫ nσ ▷ sb' ≫ (α_ _ _ _).hom ≫ sa ◁ nσ' ≫ (α_ _ _ _).inv) ≫
        Γa ▷ sf) :
    sf ◁ (kb.hom ▷ tb' ≫ sb ◁ kb'.hom ≫ Γb) ≫ (ρ_ sf).hom =
      (α_ _ _ _).inv ≫ (sf ◁ kb.hom ≫ nσ ≫ ka.inv ▷ sf') ▷ tb' ≫ (α_ _ _ _).hom ≫
        ta ◁ (sf' ◁ kb'.hom ≫ nσ' ≫ ka'.inv ▷ sf) ≫ (α_ _ _ _).inv ≫
          (ka.hom ▷ ta' ≫ sa ◁ ka'.hom ≫ Γa) ▷ sf ≫ (λ_ sf).hom := by
  symm
  calc
    _ = 𝟙 _ ⊗≫ sf ◁ kb.hom ▷ tb' ⊗≫ nσ ▷ tb' ⊗≫
          (ka.inv ▷ (sf' ≫ tb') ≫ ta ◁ (sf' ◁ kb'.hom ≫ nσ' ≫ ka'.inv ▷ sf)) ⊗≫
          ka.hom ▷ (ta' ≫ sf) ⊗≫ sa ◁ ka'.hom ▷ sf ⊗≫ Γa ▷ sf ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ sf ◁ kb.hom ▷ tb' ⊗≫ nσ ▷ tb' ⊗≫ sa ◁ sf' ◁ kb'.hom ⊗≫ sa ◁ nσ' ⊗≫
          sa ◁ ka'.inv ▷ sf ⊗≫ (ka.inv ≫ ka.hom) ▷ (ta' ≫ sf) ⊗≫ sa ◁ ka'.hom ▷ sf ⊗≫
          Γa ▷ sf ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ sf ◁ kb.hom ▷ tb' ⊗≫ nσ ▷ tb' ⊗≫ sa ◁ sf' ◁ kb'.hom ⊗≫ sa ◁ nσ' ⊗≫
          sa ◁ (ka'.inv ≫ ka'.hom) ▷ sf ⊗≫ Γa ▷ sf ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id]; bicategory
    _ = 𝟙 _ ⊗≫ sf ◁ kb.hom ▷ tb' ⊗≫ (nσ ▷ tb' ≫ (sa ≫ sf') ◁ kb'.hom) ⊗≫ sa ◁ nσ' ⊗≫
          Γa ▷ sf ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id]; bicategory
    _ = 𝟙 _ ⊗≫ sf ◁ kb.hom ▷ tb' ⊗≫ (sf ≫ sb) ◁ kb'.hom ⊗≫
          (((α_ _ _ _).inv ≫ nσ ▷ sb' ≫ (α_ _ _ _).hom ≫ sa ◁ nσ' ≫ (α_ _ _ _).inv) ≫
            Γa ▷ sf) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by rw [← hΓ]; bicategory

variable
  (nat_nat : ∀ {a b : 𝒳} {f g : a ⟶ b} (β : f ⟶ g),
    𝔉.map₂ (S.map₂ β) ▷ σapp b ≫ σnat g = σnat f ≫ σapp a ◁ 𝔉.map₂ (S'.map₂ β))
  (nat_id : ∀ a : 𝒳, σnat (𝟙 a) ≫ σapp a ◁ (𝔉.map₂ (S'.mapId a) ≫ (𝔉.mapId _).hom) =
    (𝔉.map₂ (S.mapId a) ≫ (𝔉.mapId _).hom) ▷ σapp a ≫ (λ_ _).hom ≫ (ρ_ _).inv)
  (nat_comp : ∀ {a b c : 𝒳} (f : a ⟶ b) (g : b ⟶ c),
    σnat (f ≫ g) ≫ σapp a ◁ (𝔉.map₂ (S'.mapComp f g) ≫ (𝔉.mapComp _ _).hom) =
      (𝔉.map₂ (S.mapComp f g) ≫ (𝔉.mapComp _ _).hom) ▷ σapp c ≫ (α_ _ _ _).hom ≫
        𝔉.map (S.map f) ◁ σnat g ≫ (α_ _ _ _).inv ≫ σnat f ▷ 𝔉.map (S'.map g) ≫
          (α_ _ _ _).hom)
  (nat_nat' : ∀ {a b : 𝒳} {f g : a ⟶ b} (β : f ⟶ g),
    𝔉.map₂ (S'.map₂ β) ▷ σ'app b ≫ σ'nat g = σ'nat f ≫ σ'app a ◁ 𝔉.map₂ (S.map₂ β))
  (nat_id' : ∀ a : 𝒳, σ'nat (𝟙 a) ≫ σ'app a ◁ (𝔉.map₂ (S.mapId a) ≫ (𝔉.mapId _).hom) =
    (𝔉.map₂ (S'.mapId a) ≫ (𝔉.mapId _).hom) ▷ σ'app a ≫ (λ_ _).hom ≫ (ρ_ _).inv)
  (nat_comp' : ∀ {a b c : 𝒳} (f : a ⟶ b) (g : b ⟶ c),
    σ'nat (f ≫ g) ≫ σ'app a ◁ (𝔉.map₂ (S.mapComp f g) ≫ (𝔉.mapComp _ _).hom) =
      (𝔉.map₂ (S'.mapComp f g) ≫ (𝔉.mapComp _ _).hom) ▷ σ'app c ≫ (α_ _ _ _).hom ≫
        𝔉.map (S'.map f) ◁ σ'nat g ≫ (α_ _ _ _).inv ≫ σ'nat f ▷ 𝔉.map (S.map g) ≫
          (α_ _ _ _).hom)

open OplaxTrans in
/-- The lift of an isomorphism `σ ≫ σ' ≅ 𝟙` (given by components `Γ` natural in the sense of
modifications) to an isomorphism of the lifted oplax transformations. -/
def liftCompIso
    (hΓ : ∀ {a b : 𝒳} (f : a ⟶ b), 𝔉.map (S.map f) ◁ (Γ b).hom ≫ (ρ_ _).hom ≫ (λ_ _).inv =
      ((α_ _ _ _).inv ≫ σnat f ▷ σ'app b ≫ (α_ _ _ _).hom ≫ σapp a ◁ σ'nat f ≫
        (α_ _ _ _).inv) ≫ (Γ a).hom ▷ 𝔉.map (S.map f)) :
    lift 𝔉 pre map_pre pre_map σapp σnat t κ nat_nat nat_id nat_comp ≫
      lift 𝔉 pre map_pre pre_map σ'app σ'nat t' κ' nat_nat' nat_id' nat_comp' ≅ 𝟙 S :=
  OplaxTrans.isoMk
    (fun a => PseudofunctorLift.preIso 𝔉 pre map_pre pre_map
      (modApp 𝔉 σapp t κ σ'app t' κ' Γ a))
    (fun {a b} f => by
      change S.map f ◁ pre (modApp 𝔉 σapp t κ σ'app t' κ' Γ b).hom ≫
          (ρ_ (S.map f)).hom ≫ (λ_ (S.map f)).inv =
        ((α_ _ _ _).inv ≫ pre (natU 𝔉 σapp σnat t κ f) ▷ t' b ≫ (α_ _ _ _).hom ≫
          t a ◁ pre (natU (S := S') (S' := S) 𝔉 σ'app σ'nat t' κ' f) ≫ (α_ _ _ _).inv) ≫
          pre (modApp 𝔉 σapp t κ σ'app t' κ' Γ a).hom ▷ S.map f
      rw [← cancel_mono (λ_ (S.map f)).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply PseudofunctorLift.map₂_injective 𝔉 pre pre_map
      simp only [PrelaxFunctor.map₂_comp, map_pre, natU, modApp, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
        whiskerLeftIso_hom, Pseudofunctor.map₂_whisker_right, Pseudofunctor.map₂_whisker_left,
        map₂_associator_inv, Pseudofunctor.map₂_associator, Pseudofunctor.map₂_left_unitor,
        Pseudofunctor.map₂_right_unitor, Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp,
        comp_whiskerRight, whiskerLeft_inv_hom_assoc, inv_hom_whiskerRight_assoc]
      congr 2
      have h := modApp_aux (κ a) (κ b) (κ' a) (κ' b) (σnat f) (σ'nat f) (Γ a).hom (Γ b).hom
        (hΓ f)
      simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc] at h
      exact h)

end Mod

end OplaxTransLift

end StringDiagrams
