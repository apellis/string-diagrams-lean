import StringDiagrams.Super.SOp
import StringDiagrams.Super.UnderlyingBicategory

/-!
# Whiskering in the 2-super-opposite

Preparation for the 2-super-opposite `𝔄^{sop}` of a 2-supercategory (J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 3.4): even isomorphisms of `𝒜`
give isomorphisms of `𝒜^{sop}` with the inverse reversed (`SOp.evenIso`), and left and right
whiskering are functors on the super-opposite hom categories (`TwoSOpAux.leftSOp`,
`TwoSOpAux.rightSOp`).
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
universe r u v w

namespace SOp
variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C] [Supercategory R C]

theorem compC_even_left {X Y Z : C} {f : Y ⟶ X}
    (hf : f ∈ parity (R := R) Y X 0) (g : Z ⟶ Y) :
    compC (R := R) f g = g ≫ f := by
  unfold compC
  rw [twist_one_of_mem hf, sign_zero, one_smul, ← Preadditive.add_comp, proj_add_proj]

theorem compC_even_right {X Y Z : C} (f : Y ⟶ X) {g : Z ⟶ Y}
    (hg : g ∈ parity (R := R) Z Y 0) : compC (R := R) f g = g ≫ f := by
  unfold compC
  rw [proj_of_mem hg, proj_of_mem_ne hg (by decide), Limits.zero_comp, add_zero]

/-- Only even isomorphisms are inverted without a Koszul correction. -/
def evenIso {X Y : C} (e : X ≅ Y) (he : e.hom ∈ parity (R := R) X Y 0) :
    (⟨X⟩ : SOp R C) ≅ ⟨Y⟩ where
  hom := sop e.inv
  inv := sop e.hom
  hom_inv_id := by
    apply hom_ext
    exact (compC_even_right e.inv he).trans e.hom_inv_id
  inv_hom_id := by
    apply hom_ext
    exact (compC_even_left he e.inv).trans e.inv_hom_id
end SOp

namespace TwoSOpAux
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- Left whiskering, bundled for `SOp.mapFunctor`. -/
def left {a b c : B} (f : a ⟶ b) : (b ⟶ c) ⥤ (a ⟶ c) where
  obj g := f ≫ g
  map η := f ◁ η
  map_id := whiskerLeft_id (R := R) f
  map_comp := whiskerLeft_comp (R := R) f

instance {a b c : B} (f : a ⟶ b) : (left (R := R) (c := c) f).Additive where
  map_add {_ _ η θ} := whiskerLeft_add (R := R) f η θ

instance {a b c : B} (f : a ⟶ b) : (left (R := R) (c := c) f).Linear R where
  map_smul η s := whiskerLeft_smul f s η

/-- Right whiskering, bundled for `SOp.mapFunctor`. -/
def right {a b c : B} (h : b ⟶ c) : (a ⟶ b) ⥤ (a ⟶ c) where
  obj f := f ≫ h
  map η := η ▷ h
  map_id f := id_whiskerRight (R := R) f h
  map_comp η θ := comp_whiskerRight (R := R) η θ h

instance {a b c : B} (h : b ⟶ c) : (right (R := R) (a := a) h).Additive where
  map_add {_ _ η θ} := add_whiskerRight (R := R) η θ h

instance {a b c : B} (h : b ⟶ c) : (right (R := R) (a := a) h).Linear R where
  map_smul η s := smul_whiskerRight s η h

/-- Functoriality includes arbitrary sums, not just homogeneous maps. -/
def leftSOp {a b c : B} (f : a ⟶ b) : SOp R (b ⟶ c) ⥤ SOp R (a ⟶ c) :=
  SOp.mapFunctor (left (R := R) f) (whiskerLeft_mem f)

/-- Functoriality includes arbitrary sums, not just homogeneous maps. -/
def rightSOp {a b c : B} (h : b ⟶ c) : SOp R (a ⟶ b) ⥤ SOp R (a ⟶ c) :=
  SOp.mapFunctor (right (R := R) h) (whiskerRight_mem h)
end TwoSOpAux
end StringDiagrams
