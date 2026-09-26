import StringDiagrams.Super.TwoEnvelopeEquivalence

/-!
# The categories `2-SCat` and `Π-2-SCat`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 2.2(iii) ("there is a 2-category `2-SCat` consisting of all 2-supercategories,
2-superfunctors and 2-natural transformations") and Section 5 ("`Π-2-SCat` is the category of
Π-2-supercategories and 2-superfunctors").

`TwoSCat R` is the type of (small, in fixed universes) 2-supercategories over `R`, and
`PiTwoSCat R` that of Π-2-supercategories (Definition 3.1). Both are categories with
2-superfunctors as morphisms (`TwoSuperfunctor.comp`, `TwoSuperfunctor.id`): the associativity
and unit laws for the composition of 2-superfunctors (`TwoSuperfunctor.comp_assoc`,
`TwoSuperfunctor.id_comp`, `TwoSuperfunctor.comp_id`) are equalities of 2-superfunctors, with the
coherence maps compared using `TwoSuperfunctor.map₂_comp`.

## The 2-categorical level

The paper's 2-category `2-SCat` has 2-natural transformations as 2-morphisms. The vertical
composite of 2-natural transformations `ℝ ⇒ 𝕊 ⇒ 𝕋` between 2-superfunctors into a 2-supercategory
`𝔅` has components `X_λ ≫ Y_λ` (`TwoNatTrans.vcomp`), so it is associative and unital only up to
the associators and unitors of `𝔅` (the invertible even supermodifications
`TwoNatTrans.associator`, `TwoNatTrans.leftUnitor`, `TwoNatTrans.rightUnitor` of
`StringDiagrams.Super.TwoHom`): the 2-superfunctors `𝔄 → 𝔅`, 2-natural transformations and
supermodifications form the 2-supercategory `𝔥𝔬𝔪(𝔄, 𝔅)` (`StringDiagrams.Super.TwoHom`), and
`2-SCat` is a 2-category (with hom categories the 1-truncations of the `𝔥𝔬𝔪(𝔄, 𝔅)`) only when
the targets are strict. The 2-categories `2-𝔖ℭ𝔄𝔗`, `Π-2-𝔖ℭ𝔄𝔗` and `Π-2-ℭ𝔄𝔗` are therefore not
bundled as Lean bicategories here; the hom-level content of Theorem 4.9 and Theorem 5.5 is in
`StringDiagrams.Super.TwoEnvelopeTwoHom` and `StringDiagrams.Super.AssociatedTwoNat`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ w₄ v₄ u₄

/-! ## Composition laws for 2-superfunctors -/

namespace TwoSuperfunctor

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  {D : Type u₃} [BicategoryStruct.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)]
  [∀ a b : D, Supercategory R (a ⟶ b)] [TwoSupercategory R D]
  {E : Type u₄} [BicategoryStruct.{w₄, v₄} E]
  [∀ a b : E, Preadditive (a ⟶ b)] [∀ a b : E, Linear R (a ⟶ b)]
  [∀ a b : E, Supercategory R (a ⟶ b)] [TwoSupercategory R E]

omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- Composition of 2-superfunctors is associative. -/
theorem comp_assoc (F : TwoSuperfunctor R B C) (G : TwoSuperfunctor R C D)
    (H : TwoSuperfunctor R D E) : (F.comp G).comp H = F.comp (G.comp H) := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    simp only [comp_mapComp, comp_map, comp_obj, Iso.trans_hom, map₂Iso_hom, comp_map₂,
      map₂_comp, Category.assoc]
  · funext a
    apply Iso.ext
    simp only [comp_mapId, comp_map, comp_obj, Iso.trans_hom, map₂Iso_hom, comp_map₂,
      map₂_comp, Category.assoc]

/-- The identity 2-superfunctor is a left unit for composition. -/
theorem id_comp (F : TwoSuperfunctor R B C) : (TwoSuperfunctor.id R B).comp F = F := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    simp only [comp_mapComp, Iso.trans_hom, map₂Iso_hom, id_mapComp, Iso.refl_hom, map₂_id,
      Category.comp_id]
  · funext a
    apply Iso.ext
    simp only [comp_mapId, Iso.trans_hom, map₂Iso_hom, id_mapId, Iso.refl_hom, map₂_id,
      Category.comp_id]

omit [TwoSupercategory R B] in
/-- The identity 2-superfunctor is a right unit for composition. -/
theorem comp_id (F : TwoSuperfunctor R B C) : F.comp (TwoSuperfunctor.id R C) = F := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    simp only [comp_mapComp, Iso.trans_hom, map₂Iso_hom, id_mapComp, Iso.refl_hom, id_map₂,
      Category.id_comp]
    exact Category.id_comp _
  · funext a
    apply Iso.ext
    simp only [comp_mapId, Iso.trans_hom, map₂Iso_hom, id_mapId, Iso.refl_hom, id_map₂,
      Category.id_comp]
    exact Category.id_comp _

end TwoSuperfunctor

/-! ## The category `2-SCat` -/

variable (R : Type w) [CommRing R]

/-- A 2-supercategory over `R` (Brundan–Ellis, Definition 2.2(i)), bundled. -/
structure TwoSCat where
  /-- The objects. -/
  carrier : Type u₁
  [str : BicategoryStruct.{w₁, v₁} carrier]
  [preadditive : ∀ a b : carrier, Preadditive (a ⟶ b)]
  [linear : ∀ a b : carrier, Linear R (a ⟶ b)]
  [super : ∀ a b : carrier, Supercategory R (a ⟶ b)]
  [twoSuper : TwoSupercategory R carrier]

namespace TwoSCat

attribute [instance] str preadditive linear super twoSuper

variable {R}

instance : CoeSort (TwoSCat.{w, w₁, v₁, u₁} R) (Type u₁) := ⟨TwoSCat.carrier⟩

variable (R) in
/-- The bundled 2-supercategory of a 2-supercategory. -/
abbrev of (B : Type u₁) [BicategoryStruct.{w₁, v₁} B] [∀ a b : B, Preadditive (a ⟶ b)]
    [∀ a b : B, Linear R (a ⟶ b)] [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B] :
    TwoSCat.{w, w₁, v₁, u₁} R :=
  ⟨B⟩

/-- **Brundan–Ellis, Definition 2.2.** The category `2-SCat` of 2-supercategories and
2-superfunctors. -/
instance : Category (TwoSCat.{w, w₁, v₁, u₁} R) where
  Hom B C := TwoSuperfunctor R B C
  id B := TwoSuperfunctor.id R B
  comp F G := F.comp G
  id_comp := TwoSuperfunctor.id_comp
  comp_id := TwoSuperfunctor.comp_id
  assoc := TwoSuperfunctor.comp_assoc

theorem hom_def (B C : TwoSCat.{w, w₁, v₁, u₁} R) : (B ⟶ C) = TwoSuperfunctor R B C := rfl

theorem id_def (B : TwoSCat.{w, w₁, v₁, u₁} R) : 𝟙 B = TwoSuperfunctor.id R B := rfl

theorem comp_def {B C D : TwoSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) (G : C ⟶ D) :
    F ≫ G = F.comp G := rfl

end TwoSCat

/-! ## The category `Π-2-SCat` -/

/-- A Π-2-supercategory over `R` (Brundan–Ellis, Definition 3.1), bundled. -/
structure PiTwoSCat extends TwoSCat.{w, w₁, v₁, u₁} R where
  [piTwo : PiTwoSupercategory R carrier]

namespace PiTwoSCat

attribute [instance] piTwo

variable {R}

instance : CoeSort (PiTwoSCat.{w, w₁, v₁, u₁} R) (Type u₁) := ⟨fun B => B.carrier⟩

variable (R) in
/-- The bundled Π-2-supercategory of a Π-2-supercategory. -/
abbrev of (B : Type u₁) [BicategoryStruct.{w₁, v₁} B] [∀ a b : B, Preadditive (a ⟶ b)]
    [∀ a b : B, Linear R (a ⟶ b)] [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
    [PiTwoSupercategory R B] : PiTwoSCat.{w, w₁, v₁, u₁} R :=
  ⟨TwoSCat.of R B⟩

/-- **Brundan–Ellis, Section 5.** The category `Π-2-SCat` of Π-2-supercategories and
2-superfunctors. -/
instance : Category (PiTwoSCat.{w, w₁, v₁, u₁} R) where
  Hom B C := TwoSuperfunctor R B C
  id B := TwoSuperfunctor.id R B
  comp F G := F.comp G
  id_comp := TwoSuperfunctor.id_comp
  comp_id := TwoSuperfunctor.comp_id
  assoc := TwoSuperfunctor.comp_assoc

theorem hom_def (B C : PiTwoSCat.{w, w₁, v₁, u₁} R) : (B ⟶ C) = TwoSuperfunctor R B C := rfl

/-- The forgetful functor `ν : Π-2-SCat → 2-SCat`. -/
@[simps]
def forget : PiTwoSCat.{w, w₁, v₁, u₁} R ⥤ TwoSCat.{w, w₁, v₁, u₁} R where
  obj B := B.toTwoSCat
  map F := F

end PiTwoSCat

end StringDiagrams

end
