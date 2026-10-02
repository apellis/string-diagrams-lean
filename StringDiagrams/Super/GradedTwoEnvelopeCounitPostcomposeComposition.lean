import StringDiagrams.Super.TwoFunctorPostcompositionComposition
import StringDiagrams.Super.GradedTwoEnvelopeCounitPasteRight

/-!
# The postcomposition compositor on the actual counit density pair

This separates the two actual postcomposed density transformations in
`counitNaturality F`. The source transport along the equality of restrictions
is retained. No equality of transformation records or full right-paste law is
asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁
variable {R : Type w} [CommRing R]
namespace QPiTwoEnvelope
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R}
  {C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  (S T : TwoSuperfunctor R (QPiTwoEnvelope R B) C)
  (hS : S.IsGraded) (hT : T.IsGraded) (h : restrict S = restrict T)
  (G : C ⟶ D)
local instance : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

/-- The separated actual density pair, still carrying the restriction transport. -/
def postcomposeComparisonDensityPair : TwoNatTrans (S.comp G.1) (T.comp G.1) :=
  TwoNatTrans.vcomp
    (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv S hS))
    (TwoNatTrans.postcompose G.1
      (TwoNatTrans.transportSource (congrArg extend h.symm) (extendRestrictNatTrans T hT)))

/-- Apply the inverse compositor to the actual chosen comparison. -/
def postcomposeComparisonIso :
    TwoNatTrans.postcompose G.1 (comparison S T hS hT h) ≅
      postcomposeComparisonDensityPair S T hS hT h G :=
  (TwoNatTrans.postcomposeVcompIso G.1 (extendRestrictNatTransInv S hS)
    (TwoNatTrans.transportSource (congrArg extend h.symm) (extendRestrictNatTrans T hT))).symm

theorem postcomposeComparisonIso_hom_isHomogeneous :
    (postcomposeComparisonIso S T hS hT h G).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.postcomposeVcompIso_inv_isHomogeneous _ _ _ G.2

theorem postcomposeComparisonIso_inv_isHomogeneous :
    (postcomposeComparisonIso S T hS hT h G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.postcomposeVcompIso_hom_isHomogeneous _ _ _ G.2

section Counit
variable {A : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : A ⟶ C)

/-- Exactly the density pair defining `counitNaturality F`, postcomposed separately. -/
def counitNaturalityPostcomposeDensityPair : TwoNatTrans
    (((mapQPi F.1).comp (counit C)).comp G.1) (((counit A).comp F.1).comp G.1) :=
  postcomposeComparisonDensityPair _ _
    ((mapQPi_isGraded F.2).comp (counit_isGraded C))
    ((counit_isGraded A).comp F.2) (counit_naturality_restrict F) G

/-- The actual counit transformation after postcomposition, not a replacement. -/
def counitNaturalityPostcomposeIso :
    TwoNatTrans.postcompose G.1 (counitNaturality F) ≅
      counitNaturalityPostcomposeDensityPair G F :=
  postcomposeComparisonIso _ _
    ((mapQPi_isGraded F.2).comp (counit_isGraded C))
    ((counit_isGraded A).comp F.2) (counit_naturality_restrict F) G

theorem counitNaturalityPostcomposeIso_hom_isHomogeneous :
    (counitNaturalityPostcomposeIso G F).hom.IsHomogeneous 0 0 :=
  postcomposeComparisonIso_hom_isHomogeneous _ _ _ _ _ _

theorem counitNaturalityPostcomposeIso_inv_isHomogeneous :
    (counitNaturalityPostcomposeIso G F).inv.IsHomogeneous 0 0 :=
  postcomposeComparisonIso_inv_isHomogeneous _ _ _ _ _ _

/-- Forward modification naturality at arbitrary shifted envelope 1-cells. -/
theorem counitNaturalityPostcomposeIso_hom_naturality
    {a b : QPiTwoEnvelope R A} (f : a ⟶ b) :
    (TwoNatTrans.postcompose G.1 (counitNaturality F)).x f ≫
        (counitNaturalityPostcomposeIso G F).hom.app a ▷ G.1.map (((counit A).comp F.1).map f) =
      G.1.map (((mapQPi F.1).comp (counit C)).map f) ◁
        (counitNaturalityPostcomposeIso G F).hom.app b ≫
          (counitNaturalityPostcomposeDensityPair G F).x f :=
  (counitNaturalityPostcomposeIso G F).hom.naturality f

/-- Inverse modification naturality at arbitrary shifted envelope 1-cells. -/
theorem counitNaturalityPostcomposeIso_inv_naturality
    {a b : QPiTwoEnvelope R A} (f : a ⟶ b) :
    (counitNaturalityPostcomposeDensityPair G F).x f ≫
        (counitNaturalityPostcomposeIso G F).inv.app a ▷ G.1.map (((counit A).comp F.1).map f) =
      G.1.map (((mapQPi F.1).comp (counit C)).map f) ◁
        (counitNaturalityPostcomposeIso G F).inv.app b ≫
          (TwoNatTrans.postcompose G.1 (counitNaturality F)).x f :=
  (counitNaturalityPostcomposeIso G F).inv.naturality f

/-- No parity or degree restriction on the input 2-morphism (in particular odd ones). -/
theorem counitNaturalityPostcomposeDensityPair_naturality
    {a b : QPiTwoEnvelope R A} {f g : a ⟶ b} (η : f ⟶ g) :
    G.1.map₂ (((mapQPi F.1).comp (counit C)).map₂ η) ▷
        (counitNaturalityPostcomposeDensityPair G F).X b ≫
          (counitNaturalityPostcomposeDensityPair G F).x g =
      (counitNaturalityPostcomposeDensityPair G F).x f ≫
        (counitNaturalityPostcomposeDensityPair G F).X a ◁
          G.1.map₂ (((counit A).comp F.1).map₂ η) :=
  (counitNaturalityPostcomposeDensityPair G F).naturality η
end Counit
end QPiTwoEnvelope
end StringDiagrams
