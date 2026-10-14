import StringDiagrams.Super.EvenModificationIso

/-!
# Zigzag composites of a unit and counit of 2-superfunctors

Let `F : 𝔄 → 𝔅` and `G : 𝔅 → 𝔄` be 2-superfunctors with transformations
`J : 1_𝔄 ⟹ F ⋙ G` and `E : G ⋙ F ⟹ 1_𝔅` (composition is written diagrammatically, so
`F ⋙ G = F.comp G` applies `F` first). The two zigzag composites are
* `LeftZigzag.zigzag F G J E : F ⟹ F`, the composite of `F ∘ J : F ⟹ F ⋙ G ⋙ F` and
  `E ∘ F : F ⋙ G ⋙ F ⟹ F`;
* `RightZigzag.zigzag F G J E : G ⟹ G`, the composite of `J ∘ G : G ⟹ G ⋙ F ⋙ G` and
  `G ∘ E : G ⋙ F ⋙ G ⟹ G`.

The triangle identities of an adjoint biequivalence are even isomorphisms from these zigzags
to the identity transformations. The legs are transported along the associativity and unit
equalities of composition of 2-superfunctors, and their components are computed by
`LeftZigzag.zigzag_X` and `RightZigzag.zigzag_X`.

`TwoSuperfunctor.IsAdjointBiequivalence F G J E` states that `F`, `G`, `J`, `E` form an adjoint
biequivalence of graded 2-supercategories: graded 2-superfunctors, a strong graded unit and counit
with strong graded inverses up to even isomorphisms, and both triangle identities up to even
isomorphisms.

`EvenIso.zigzagCancel` transports an isomorphism `L ∘ E ≅ 1` to the composite of
`L ∘ F` with the counit leg of the left zigzag. It is used for the triangle identities of the
Chevalley involution of arXiv:1701.04133v2, Proposition 9.3.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct
universe r u v w u' v' w'
variable {R : Type r} [CommRing R]
  {A : Type u} [BicategoryStruct.{w, v} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A]
  {B : Type u'} [BicategoryStruct.{w', v'} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  (F : TwoSuperfunctor R A B) (G : TwoSuperfunctor R B A)
  (J : TwoNatTrans (TwoSuperfunctor.id R A) (F.comp G))
  (E : TwoNatTrans (G.comp F) (TwoSuperfunctor.id R B))

namespace LeftZigzag

/-- The leg `F ∘ J : F ⟹ F ⋙ (G ⋙ F)`. -/
def unitLeg : TwoNatTrans F (F.comp (G.comp F)) :=
  TwoNatTrans.rebase (TwoSuperfunctor.id_comp F) (TwoSuperfunctor.comp_assoc F G F)
    (TwoNatTrans.postcompose F J)

/-- The leg `E ∘ F : F ⋙ (G ⋙ F) ⟹ F`. -/
def counitLeg : TwoNatTrans (F.comp (G.comp F)) F :=
  TwoNatTrans.rebase rfl (TwoSuperfunctor.comp_id F) (TwoNatTrans.precompose F E)

/-- The zigzag `F ⟹ F ⋙ G ⋙ F ⟹ F`. -/
def zigzag : TwoNatTrans F F := (unitLeg F G J).vcomp (counitLeg F G E)

theorem unitLeg_X (a : A) : (unitLeg F G J).X a = F.map (J.X a) :=
  eq_of_heq (TwoNatTrans.rebase_X _ _ _ a)

omit [TwoSupercategory R A] in
theorem counitLeg_X (a : A) : (counitLeg F G E).X a = E.X (F.obj a) :=
  eq_of_heq (TwoNatTrans.rebase_X _ _ _ a)

theorem zigzag_X (a : A) : (zigzag F G J E).X a = F.map (J.X a) ≫ E.X (F.obj a) := by
  change (unitLeg F G J).X a ≫ (counitLeg F G E).X a = _
  rw [unitLeg_X, counitLeg_X]
  rfl

theorem unitLeg_x {a b : A} (f : a ⟶ b) :
    HEq ((unitLeg F G J).x f) (TwoNatTrans.postcomposeCell F J f) :=
  TwoNatTrans.rebase_x (TwoSuperfunctor.id_comp F)
    (TwoSuperfunctor.comp_assoc F G F) (TwoNatTrans.postcompose F J) f

omit [TwoSupercategory R A] in
theorem counitLeg_x {a b : A} (f : a ⟶ b) :
    HEq ((counitLeg F G E).x f) (E.x (F.map f)) :=
  TwoNatTrans.rebase_x rfl (TwoSuperfunctor.comp_id F) (TwoNatTrans.precompose F E) f
end LeftZigzag

namespace RightZigzag

/-- The leg `J ∘ G : G ⟹ G ⋙ (F ⋙ G)`. -/
def unitLeg : TwoNatTrans G (G.comp (F.comp G)) :=
  TwoNatTrans.rebase (TwoSuperfunctor.comp_id G) rfl (TwoNatTrans.precompose G J)

/-- The leg `G ∘ E : G ⋙ (F ⋙ G) ⟹ G`. -/
def counitLeg : TwoNatTrans (G.comp (F.comp G)) G :=
  TwoNatTrans.rebase (TwoSuperfunctor.comp_assoc G F G) (TwoSuperfunctor.id_comp G)
    (TwoNatTrans.postcompose G E)

/-- The zigzag `G ⟹ G ⋙ F ⋙ G ⟹ G`. -/
def zigzag : TwoNatTrans G G := (unitLeg F G J).vcomp (counitLeg F G E)

omit [TwoSupercategory R B] in
theorem unitLeg_X (b : B) : (unitLeg F G J).X b = J.X (G.obj b) :=
  eq_of_heq (TwoNatTrans.rebase_X _ _ _ b)

theorem counitLeg_X (b : B) : (counitLeg F G E).X b = G.map (E.X b) :=
  eq_of_heq (TwoNatTrans.rebase_X _ _ _ b)

theorem zigzag_X (b : B) : (zigzag F G J E).X b = J.X (G.obj b) ≫ G.map (E.X b) := by
  change (unitLeg F G J).X b ≫ (counitLeg F G E).X b = _
  rw [unitLeg_X, counitLeg_X]
  rfl
end RightZigzag

variable {F G} in
/-- An even isomorphism `L ∘ E ≅ 1`, precomposed with `F`, as an isomorphism from the
composite of `L ∘ F` and the counit leg of the left zigzag to the identity of `F`. -/
def EvenIso.zigzagCancel [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    (L : TwoNatTrans (TwoSuperfunctor.id R B) (G.comp F))
    (e : EvenIso (L.vcomp E) (TwoNatTrans.id (TwoSuperfunctor.id R B))) :
    EvenIso
      ((TwoNatTrans.rebase (TwoSuperfunctor.comp_id F) rfl
        (TwoNatTrans.precompose F L)).vcomp (LeftZigzag.counitLeg F G E))
      (TwoNatTrans.id F) :=
  EvenIso.rebaseCancel (TwoSuperfunctor.comp_id F) rfl _ _ (EvenIso.precomposeCancel F L E e)

section Biequivalence
variable [∀ a b : A, GradedSupercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]

/-- `F : 𝔄 → 𝔅` and `G : 𝔅 → 𝔄`, with unit `J : 1 ⟹ F ⋙ G` and counit `E : G ⋙ F ⟹ 1`,
form an adjoint biequivalence of graded 2-supercategories. Both 2-superfunctors are graded.
The unit and counit are strong and graded, and have strong graded inverses up to even
isomorphisms (`EvenIso`). Both zigzags (`LeftZigzag.zigzag`, `RightZigzag.zigzag`) are evenly
isomorphic to identity transformations. -/
structure TwoSuperfunctor.IsAdjointBiequivalence : Prop where
  left_isGraded : F.IsGraded
  right_isGraded : G.IsGraded
  unit_isStrong : J.IsStrong
  unit_isGraded : J.IsGraded
  counit_isStrong : E.IsStrong
  counit_isGraded : E.IsGraded
  unit_invertible : ∃ K : TwoNatTrans (F.comp G) (TwoSuperfunctor.id R A),
    K.IsStrong ∧ K.IsGraded ∧ Nonempty (EvenIso (J.vcomp K) (TwoNatTrans.id _)) ∧
      Nonempty (EvenIso (K.vcomp J) (TwoNatTrans.id _))
  counit_invertible : ∃ L : TwoNatTrans (TwoSuperfunctor.id R B) (G.comp F),
    L.IsStrong ∧ L.IsGraded ∧ Nonempty (EvenIso (E.vcomp L) (TwoNatTrans.id _)) ∧
      Nonempty (EvenIso (L.vcomp E) (TwoNatTrans.id _))
  left_triangle : Nonempty (EvenIso (LeftZigzag.zigzag F G J E) (TwoNatTrans.id F))
  right_triangle : Nonempty (EvenIso (RightZigzag.zigzag F G J E) (TwoNatTrans.id G))
end Biequivalence
end StringDiagrams
