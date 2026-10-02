import StringDiagrams.Super.GradedTwoEnvelopeCounitComposition
import StringDiagrams.Super.TwoFunctorPrecomposition
import StringDiagrams.Super.TwoFunctorPostcomposition

/-!
# The genuine composite-functor counit paste

The two legs are actual precomposition and postcomposition of the counit
comparisons. Equalities of complete 2-superfunctor records normalize all
three boundaries. Their vertical composite retains the target associators,
unitors, and both compositor factors in postcomposition.

This constructs a strong graded transformation with precisely the endpoints
of `counitNaturality (F ≫ G)`. An invertible supermodification identifying
these two transformations is not asserted: `comparisonCompIso` alone does
not identify the functor-whiskered legs with chosen density comparisons.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁
variable {R : Type w} [CommRing R]

namespace TwoNatTrans
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R} {C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  {S T S' T' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}

/-- Boundary equality transport preserves grading of the full transformation. -/
theorem transportBoundary_isGraded (h : S = S') (k : T = T')
    (θ : TwoNatTrans S T) (hθ : θ.IsGraded) :
    (transportBoundary h k θ).IsGraded := by
  cases h
  cases k
  exact hθ

/-- Boundary equality transport preserves invertibility of every naturality cell. -/
theorem transportBoundary_isStrong (h : S = S') (k : T = T')
    (θ : TwoNatTrans S T) (hθ : θ.IsStrong) :
    (transportBoundary h k θ).IsStrong := by
  cases h
  cases k
  exact hθ
/-- Transport only retypes the object component; it does not replace it. -/
theorem transportBoundary_X_heq (h : S = S') (k : T = T')
    (θ : TwoNatTrans S T) (a : QPiTwoEnvelope R B) :
    HEq ((transportBoundary h k θ).X a) (θ.X a) := by
  cases h
  cases k
  rfl
end TwoNatTrans

namespace QPiTwoEnvelope
set_option backward.isDefEq.respectTransparency false
variable {B C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) (G : C ⟶ D)

/-- The left-whiskered source is the direct composite square's source. -/
theorem counitPaste_source :
    (mapQPi F.1).comp ((mapQPi G.1).comp (counit D)) =
      (mapQPi (F ≫ G).1).comp (counit D) := by
  change _ = (mapQPi (F.1.comp G.1)).comp (counit D)
  rw [mapQPi_comp, TwoSuperfunctor.comp_assoc]

/-- The right-whiskered source matches the left-whiskered target. -/
theorem counitPaste_middle :
    ((mapQPi F.1).comp (counit C)).comp G.1 =
      (mapQPi F.1).comp ((counit C).comp G.1) :=
  TwoSuperfunctor.comp_assoc _ _ _

/-- The right-whiskered target is the direct composite square's target. -/
theorem counitPaste_target :
    ((counit B).comp F.1).comp G.1 = (counit B).comp (F ≫ G).1 :=
  TwoSuperfunctor.comp_assoc _ _ _

/-- The actual left leg, with its outer source boundary normalized. -/
def counitPasteLeft : TwoNatTrans
    ((mapQPi (F ≫ G).1).comp (counit D))
    ((mapQPi F.1).comp ((counit C).comp G.1)) :=
  TwoNatTrans.transportBoundary (counitPaste_source F G) rfl
    (TwoNatTrans.precompose (mapQPi F.1) (counitNaturality G))

/-- The actual right leg, with both middle and outer boundaries normalized. -/
def counitPasteRight : TwoNatTrans
    ((mapQPi F.1).comp ((counit C).comp G.1))
    ((counit B).comp (F ≫ G).1) :=
  TwoNatTrans.transportBoundary (counitPaste_middle F G) (counitPaste_target F G)
    (TwoNatTrans.postcompose G.1 (counitNaturality F))

theorem counitPasteLeft_isGraded : (counitPasteLeft F G).IsGraded :=
  TwoNatTrans.transportBoundary_isGraded _ _ _
    (TwoNatTrans.precompose_isGraded _ (counitNaturality_isGraded G))

theorem counitPasteLeft_isStrong : (counitPasteLeft F G).IsStrong :=
  TwoNatTrans.transportBoundary_isStrong _ _ _
    (TwoNatTrans.precompose_isStrong _ (counitNaturality_isStrong G))

theorem counitPasteRight_isGraded : (counitPasteRight F G).IsGraded :=
  TwoNatTrans.transportBoundary_isGraded _ _ _
    (TwoNatTrans.postcompose_isGraded _ G.2 (counitNaturality_isGraded F))

theorem counitPasteRight_isStrong : (counitPasteRight F G).IsStrong :=
  TwoNatTrans.transportBoundary_isStrong _ _ _
    (TwoNatTrans.postcompose_isStrong _ (counitNaturality_isStrong F))

/-- Paste the genuine functor-whiskered counit squares, not substitute comparisons. -/
def counitNaturalityPaste : TwoNatTrans
    ((mapQPi (F ≫ G).1).comp (counit D)) ((counit B).comp (F ≫ G).1) :=
  TwoNatTrans.vcomp (counitPasteLeft F G) (counitPasteRight F G)

theorem counitPasteLeft_X (a : QPiTwoEnvelope R B) :
    (counitPasteLeft F G).X a = (counitNaturality G).X ((mapQPi F.1).obj a) :=
  eq_of_heq (TwoNatTrans.transportBoundary_X_heq _ _ _ a)

theorem counitPasteRight_X (a : QPiTwoEnvelope R B) :
    (counitPasteRight F G).X a = G.1.map ((counitNaturality F).X a) :=
  eq_of_heq (TwoNatTrans.transportBoundary_X_heq _ _ _ a)

/-- The object component uses precisely the two functor-whiskered components. -/
theorem counitNaturalityPaste_X (a : QPiTwoEnvelope R B) :
    (counitNaturalityPaste F G).X a =
      (counitNaturality G).X ((mapQPi F.1).obj a) ≫ G.1.map ((counitNaturality F).X a) := by
  change (counitPasteLeft F G).X a ≫ (counitPasteRight F G).X a = _
  rw [counitPasteLeft_X, counitPasteRight_X]

theorem counitNaturalityPaste_isGraded : (counitNaturalityPaste F G).IsGraded :=
  TwoNatTrans.IsGraded.vcomp (counitPasteLeft_isGraded F G) (counitPasteRight_isGraded F G)

theorem counitNaturalityPaste_isStrong : (counitNaturalityPaste F G).IsStrong :=
  TwoNatTrans.vcomp_isStrong (counitPasteLeft_isStrong F G) (counitPasteRight_isStrong F G)

/-- The paste's naturality is for all 2-morphisms, without evenness or degree assumptions. -/
theorem counitNaturalityPaste_naturality {a b : QPiTwoEnvelope R B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    ((mapQPi (F ≫ G).1).comp (counit D)).map₂ η ▷
        (counitNaturalityPaste F G).X b ≫ (counitNaturalityPaste F G).x g =
      (counitNaturalityPaste F G).x f ≫ (counitNaturalityPaste F G).X a ◁
        ((counit B).comp (F ≫ G).1).map₂ η :=
  (counitNaturalityPaste F G).naturality η

end QPiTwoEnvelope
end StringDiagrams
