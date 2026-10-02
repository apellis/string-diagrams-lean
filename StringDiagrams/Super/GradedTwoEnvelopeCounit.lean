import StringDiagrams.Super.GradedTwoEnvelopeCoherence

/-!
# Evaluation counits for the graded two-envelope

The counit evaluates formal shifts using the *chosen* `(Q, Π)`-structure, via
Lemma 6.11, rather than including objects with `J`. Its right triangle is a
strict equality of graded 2-superfunctors. Naturality and the left triangle
are comparison 2-natural transformations, not equalities in the existing
1-truncations: their morphisms do not preserve chosen shifts strictly.
This file does not assert an ordinary adjunction or a global graded 2-adjunction.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁
variable {R : Type w} [CommRing R]

namespace TwoNatTrans
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R} {C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  {F F' G H : TwoSuperfunctor R (QPiTwoEnvelope R B) C}

/-- Transport the source functor of an actual transformation. -/
def transportSource (h : F = F') (θ : TwoNatTrans F G) : TwoNatTrans F' G := h ▸ θ

theorem transportSource_isGraded (h : F = F') (θ : TwoNatTrans F G) (hθ : θ.IsGraded) :
    (transportSource h θ).IsGraded := by
  cases h
  exact hθ

theorem transportSource_isStrong (h : F = F') (θ : TwoNatTrans F G) (hθ : θ.IsStrong) :
    (transportSource h θ).IsStrong := by
  cases h
  exact hθ

set_option backward.isDefEq.respectTransparency false in
theorem vcomp_isStrong {θ : TwoNatTrans F G} {ψ : TwoNatTrans G H}
    (hθ : θ.IsStrong) (hψ : ψ.IsStrong) : (vcomp θ ψ).IsStrong := by
  intro a b f
  rw [vcomp_x]
  have := hθ f
  have := hψ f
  have : IsIso (θ.x f ▷ ψ.X b) :=
    (whiskerRightIso (R := R) (asIso (θ.x f)) (ψ.X b)).isIso_hom
  have : IsIso (θ.X a ◁ ψ.x f) :=
    (whiskerLeftIso (R := R) (θ.X a) (asIso (ψ.x f))).isIso_hom
  infer_instance
end TwoNatTrans

namespace QPiTwoEnvelope

/-- Evaluation of formal shifts in an existing graded `(Q, Π)`-2-supercategory. -/
def counit (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    TwoSuperfunctor R (QPiTwoEnvelope R B) B :=
  extendQPi (TwoSuperfunctor.id R B)

theorem counit_isGraded (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) : (counit B).IsGraded :=
  extendQPi_isGraded _ TwoSuperfunctor.id_isGraded

/-- The actual evaluation counit evaluates both nontrivial formal shifts. -/
theorem counit_map_one_one (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) {a b : B} (f : a ⟶ b) :
    (counit B).map (⟨1, ⟨1, f⟩⟩ : (⟨⟨a⟩⟩ : QPiTwoEnvelope R B) ⟶ ⟨⟨b⟩⟩) =
      (f ≫ QPiTwoSupercategory.q (R := R) b) ≫ PiTwoSupercategory.pi (R := R) b := rfl

/-- The right triangle, as an equality of complete 2-superfunctors. -/
theorem counit_right_triangle (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (twoJ R B).comp (counit B) = TwoSuperfunctor.id R B :=
  twoJ_comp_extendQPi _

/-- Both sides of the counit naturality square restrict to the same functor. -/
theorem counit_naturality_restrict {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
    (F : B ⟶ C) :
    restrict ((mapQPi F.1).comp (counit C)) = restrict ((counit B).comp F.1) := by
  simp only [restrict_eq_comp, ← TwoSuperfunctor.comp_assoc, twoJ_naturality]
  rw [TwoSuperfunctor.comp_assoc, counit_right_triangle, TwoSuperfunctor.comp_id,
    counit_right_triangle, TwoSuperfunctor.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The left triangle restricts to the identity on the image of `J`. -/
theorem counit_left_triangle_restrict (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    restrict ((mapQPi (twoJ R B)).comp (counit (GTwoSCat.envelope.obj B))) =
      restrict (TwoSuperfunctor.id R (QPiTwoEnvelope R B)) := by
  simp only [restrict_eq_comp, ← TwoSuperfunctor.comp_assoc, twoJ_naturality]
  rw [TwoSuperfunctor.comp_assoc]
  exact congrArg ((twoJ R B).comp) (counit_right_triangle (GTwoSCat.envelope.obj B))

section Comparison
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R} {C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  (S T : TwoSuperfunctor R (QPiTwoEnvelope R B) C)
  (hS : S.IsGraded) (hT : T.IsGraded) (h : restrict S = restrict T)

/-- Two graded functors with the same restriction are compared through their
common extension. This uses the actual density transformations of Lemma 6.11. -/
def comparison : TwoNatTrans S T := by
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
    fun a b => QPiTwoSupercategory.homQPiLeft a b
  exact TwoNatTrans.vcomp (extendRestrictNatTransInv S hS)
    (TwoNatTrans.transportSource (congrArg extend h.symm) (extendRestrictNatTrans T hT))

theorem comparison_isGraded : (comparison S T hS hT h).IsGraded := by
  let : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
    fun a b => QPiTwoSupercategory.homQPiLeft a b
  apply TwoNatTrans.IsGraded.vcomp
  · exact extendRestrictNatTransInv_isGraded S hS
  · exact TwoNatTrans.transportSource_isGraded _ _ (extendRestrictNatTrans_isGraded T hT)

theorem comparison_isStrong : (comparison S T hS hT h).IsStrong := by
  let : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
    fun a b => QPiTwoSupercategory.homQPiLeft a b
  apply TwoNatTrans.vcomp_isStrong
  · exact extendRestrictNatTransInv_isStrong S hS
  · exact TwoNatTrans.transportSource_isStrong _ _ (extendRestrictNatTrans_isStrong T hT)

end Comparison

/-- Naturality of evaluation, as an actual graded 2-natural comparison. -/
def counitNaturality {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    TwoNatTrans ((mapQPi F.1).comp (counit C)) ((counit B).comp F.1) :=
  comparison (B := B.toGTwoSCat) _ _
    ((mapQPi_isGraded F.2).comp (counit_isGraded C))
    ((counit_isGraded B).comp F.2) (counit_naturality_restrict F)

theorem counitNaturality_isGraded {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    (counitNaturality F).IsGraded := comparison_isGraded _ _ _ _ _

/-- The left triangle as an actual 2-natural comparison, not an equality. -/
def counitLeftTriangle (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    TwoNatTrans ((mapQPi (twoJ R B)).comp (counit (GTwoSCat.envelope.obj B)))
      (TwoSuperfunctor.id R (QPiTwoEnvelope R B)) :=
  comparison (B := B) (C := GTwoSCat.envelope.obj B) _ _
    ((mapQPi_isGraded twoJ_isGraded).comp (counit_isGraded _))
    TwoSuperfunctor.id_isGraded (counit_left_triangle_restrict B)

theorem counitNaturality_isStrong {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    (counitNaturality F).IsStrong := comparison_isStrong _ _ _ _ _

/-- A comparison in the opposite direction of the counit square. -/
def counitNaturalityInv {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    TwoNatTrans ((counit B).comp F.1) ((mapQPi F.1).comp (counit C)) :=
  comparison (B := B.toGTwoSCat) _ _
    ((counit_isGraded B).comp F.2)
    ((mapQPi_isGraded F.2).comp (counit_isGraded C)) (counit_naturality_restrict F).symm

/-- A comparison in the opposite direction of the left triangle. -/
def counitLeftTriangleInv (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    TwoNatTrans (TwoSuperfunctor.id R (QPiTwoEnvelope R B))
      ((mapQPi (twoJ R B)).comp (counit (GTwoSCat.envelope.obj B))) :=
  comparison (B := B) (C := GTwoSCat.envelope.obj B) _ _
    TwoSuperfunctor.id_isGraded
    ((mapQPi_isGraded twoJ_isGraded).comp (counit_isGraded _)) (counit_left_triangle_restrict B).symm

end QPiTwoEnvelope

namespace QPiTwoGSCat
/-- The evaluation component is a morphism of the existing 1-truncation.
It is not asserted to be a natural transformation there. -/
def envelopeCounitApp (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    GTwoSCat.envelope.obj (forget.obj B) ⟶ B :=
  ⟨QPiTwoEnvelope.counit B, QPiTwoEnvelope.counit_isGraded B⟩

/-- The strict right triangle for the bundled unit and evaluation component. -/
theorem envelopeCounitApp_right_triangle (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    GTwoSCat.envelopeUnit.app (forget.obj B) ≫ forget.map (envelopeCounitApp B) =
      𝟙 (forget.obj B) :=
  Subtype.ext (QPiTwoEnvelope.counit_right_triangle B)
end QPiTwoGSCat
end StringDiagrams
