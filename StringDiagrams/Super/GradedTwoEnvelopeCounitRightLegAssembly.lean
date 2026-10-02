import StringDiagrams.Super.GradedTwoEnvelopeCounitPostcomposeBridgeCoherence

/-!
# Assembly of the actual right counit-paste leg

The inverse and transported forward factorizations are pasted using the proved
both-boundary bridge identification. The target equality is moved onto the
remaining forward density, not discarded. Finally both external boundaries
are normalized. No strict counit naturality or global adjunction is asserted.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁
variable {R : Type w} [CommRing R]
set_option backward.isDefEq.respectTransparency false

namespace TwoNatTrans
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R}
  {C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  {S U E E' K K' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}

/-- Cancel identified bridges with both endpoint equalities retained.
Path induction applies only to the bridge endpoints, never to `S = U`. -/
def pasteAlignedBridgesIso (p : K = K') (q : E = E')
    (a : TwoNatTrans S E) (b : TwoNatTrans E K)
    (c : TwoNatTrans K E) (c' : TwoNatTrans K' E') (d : TwoNatTrans E' U)
    (hc : transportBoundary p q c = c') (e : vcomp b c ≅ id E) :
    vcomp (vcomp a b) (vcomp (transportSource p.symm c') d) ≅
      vcomp a (transportSource q.symm d) := by
  cases p
  cases q
  cases hc
  exact pasteComparison a b c d e

theorem pasteAlignedBridgesIso_hom_isHomogeneous (p : K = K') (q : E = E')
    (a : TwoNatTrans S E) (b : TwoNatTrans E K)
    (c : TwoNatTrans K E) (c' : TwoNatTrans K' E') (d : TwoNatTrans E' U)
    (hc : transportBoundary p q c = c') (e : vcomp b c ≅ id E)
    (he : e.hom.IsHomogeneous 0 0) :
    (pasteAlignedBridgesIso p q a b c c' d hc e).hom.IsHomogeneous 0 0 := by
  cases p
  cases q
  cases hc
  exact pasteComparison_hom_isHomogeneous a b c d e he

/-- Retype an actual invertible modification along both external boundaries. -/
def boundaryTransportIso {S' U' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}
    (p : S = S') (q : U = U') {θ ψ : TwoNatTrans S U} (e : θ ≅ ψ) :
    transportBoundary p q θ ≅ transportBoundary p q ψ := by
  cases p
  cases q
  exact e

theorem boundaryTransportIso_hom_isHomogeneous
    {S' U' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}
    (p : S = S') (q : U = U') {θ ψ : TwoNatTrans S U} (e : θ ≅ ψ)
    (he : e.hom.IsHomogeneous 0 0) :
    (boundaryTransportIso p q e).hom.IsHomogeneous 0 0 := by
  cases p
  cases q
  exact he

end TwoNatTrans
namespace QPiTwoEnvelope
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R}
  {C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  (S T : TwoSuperfunctor R (QPiTwoEnvelope R B) C)
  (hS : S.IsGraded) (hT : T.IsGraded) (h : restrict S = restrict T) (G : C ⟶ D)
local instance : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b
local instance : ∀ a b : D, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

/-- The actual separated density pair with both published factorizations applied. -/
def postcomposeComparisonFactoredPair : TwoNatTrans (S.comp G.1) (T.comp G.1) :=
  TwoNatTrans.vcomp
    (TwoNatTrans.vcomp (extendRestrictNatTransInv (S.comp G.1) (hS.comp G.2))
      (postcomposeDensityBridgeInv S hS G))
    (TwoNatTrans.vcomp
      (TwoNatTrans.transportSource (postcomposeBridge_source S T h G).symm
        (postcomposeDensityBridge T hT G))
      (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2)))

/-- Apply the transported forward factorization after the actual inverse one. -/
def postcomposeComparisonDensityPairFactorizationIso :
    postcomposeComparisonDensityPair S T hS hT h G ≅
      postcomposeComparisonFactoredPair S T hS hT h G :=
  postcomposeComparisonDensityPairInverseIso T hT G S hS h ≪≫
    TwoSupercategory.whiskerLeftIso (R := R)
      (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D) _
      (postcomposeTransportedDensityFactorizationIso S T hT h G)

theorem postcomposeComparisonDensityPairFactorizationIso_hom_isHomogeneous :
    (postcomposeComparisonDensityPairFactorizationIso S T hS hT h G).hom.IsHomogeneous 0 0 := by
  intro a
  have hi := postcomposeComparisonDensityPairInverseIso_hom_isHomogeneous T hT G S hS h a
  have hf := postcomposeTransportedDensityFactorizationIso_hom_isHomogeneous S T hT h G a
  exact ⟨by simpa only [zero_add] using! comp_mem hi.1 (whiskerLeft_mem _ hf.1),
    by simpa only [zero_add] using! comp_mem_degree hi.2
        (GradedTwoSupercategory.whiskerLeft_mem_degree _ hf.2)⟩

/-- Cancel the actual reverse/forward bridges through their target transport.
The result is exactly the chosen comparison of the postcomposed functors. -/
def postcomposeComparisonBridgeCancellationIso :
    postcomposeComparisonFactoredPair S T hS hT h G ≅
      comparison (S.comp G.1) (T.comp G.1) (hS.comp G.2) (hT.comp G.2)
        (postcompose_restrict_congr S T h G) :=
  TwoNatTrans.pasteAlignedBridgesIso
    (postcomposeBridge_source S T h G) (postcomposeBridge_target S T h G)
    (extendRestrictNatTransInv (S.comp G.1) (hS.comp G.2))
    (postcomposeDensityBridgeInv S hS G) (postcomposeDensityBridge S hS G)
    (postcomposeDensityBridge T hT G)
    (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2))
    (postcomposeDensityBridge_transportBoundary S T hS hT h G)
    (postcomposeDensityBridgeUnitIso S hS G)

theorem postcomposeComparisonBridgeCancellationIso_hom_isHomogeneous :
    (postcomposeComparisonBridgeCancellationIso S T hS hT h G).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.pasteAlignedBridgesIso_hom_isHomogeneous _ _ _ _ _ _ _ _ _
    (postcomposeDensityBridgeUnitIso_hom_isHomogeneous S hS G)

/-- Postcomposition of the original comparison agrees up to even modification
with the original chosen comparison on the postcomposed boundaries. -/
def postcomposeComparisonAssemblyIso :
    TwoNatTrans.postcompose G.1 (comparison S T hS hT h) ≅
      comparison (S.comp G.1) (T.comp G.1) (hS.comp G.2) (hT.comp G.2)
        (postcompose_restrict_congr S T h G) :=
  postcomposeComparisonIso S T hS hT h G ≪≫
    postcomposeComparisonDensityPairFactorizationIso S T hS hT h G ≪≫
    postcomposeComparisonBridgeCancellationIso S T hS hT h G

theorem postcomposeComparisonAssemblyIso_hom_isHomogeneous :
    (postcomposeComparisonAssemblyIso S T hS hT h G).hom.IsHomogeneous 0 0 := by
  intro a
  have h₁ := postcomposeComparisonIso_hom_isHomogeneous S T hS hT h G a
  have h₂ := postcomposeComparisonDensityPairFactorizationIso_hom_isHomogeneous S T hS hT h G a
  have h₃ := postcomposeComparisonBridgeCancellationIso_hom_isHomogeneous S T hS hT h G a
  exact ⟨by simpa only [zero_add] using! comp_mem h₁.1 (comp_mem h₂.1 h₃.1),
    by simpa only [zero_add] using! comp_mem_degree h₁.2 (comp_mem_degree h₂.2 h₃.2)⟩

theorem postcomposeComparisonAssemblyIso_inv_isHomogeneous :
    (postcomposeComparisonAssemblyIso S T hS hT h G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeComparisonAssemblyIso_hom_isHomogeneous S T hS hT h G)

section Counit
variable {A : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : A ⟶ C)

/-- Assembly for the original counit square, before external normalization. -/
def counitNaturalityPostcomposeAssemblyIso :
    TwoNatTrans.postcompose G.1 (counitNaturality F) ≅
      comparison (((mapQPi F.1).comp (counit C)).comp G.1)
        (((counit A).comp F.1).comp G.1)
        (((mapQPi_isGraded F.2).comp (counit_isGraded C)).comp G.2)
        (((counit_isGraded A).comp F.2).comp G.2)
        (postcompose_restrict_congr _ _ (counit_naturality_restrict F) G) :=
  postcomposeComparisonAssemblyIso _ _ _ _ (counit_naturality_restrict F) G

theorem counitNaturalityPostcomposeAssemblyIso_hom_isHomogeneous :
    (counitNaturalityPostcomposeAssemblyIso G F).hom.IsHomogeneous 0 0 :=
  postcomposeComparisonAssemblyIso_hom_isHomogeneous _ _ _ _ _ _

/-- The actual right leg and the original comparison, with both external
boundaries normalized by the original associativity equalities. -/
def counitPasteRightIso (F : A ⟶ C) (G : C ⟶ D) : counitPasteRight F G ≅ counitPasteRightComparison F G :=
  TwoNatTrans.boundaryTransportIso (counitPaste_middle F G) (counitPaste_target F G)
    (counitNaturalityPostcomposeAssemblyIso G F) ≪≫
  eqToIso (comparison_transportBoundary _ _ _ _ _
    (counitPaste_middle F G) (counitPaste_target F G) _ _ (counitPasteRight_restrict F G))

theorem counitPasteRightIso_hom_isHomogeneous (F : A ⟶ C) (G : C ⟶ D) :
    (counitPasteRightIso F G).hom.IsHomogeneous 0 0 := by
  intro a
  have h₁ := TwoNatTrans.boundaryTransportIso_hom_isHomogeneous
    (counitPaste_middle F G) (counitPaste_target F G)
    (counitNaturalityPostcomposeAssemblyIso G F)
    (counitNaturalityPostcomposeAssemblyIso_hom_isHomogeneous G F) a
  have h₂ := TwoNatTrans.eqToIso_hom_isHomogeneous
    (comparison_transportBoundary _ _
      (((mapQPi_isGraded F.2).comp (counit_isGraded C)).comp G.2)
      (((counit_isGraded A).comp F.2).comp G.2)
      (postcompose_restrict_congr _ _ (counit_naturality_restrict F) G)
      (counitPaste_middle F G) (counitPaste_target F G)
      ((mapQPi_isGraded F.2).comp ((counit_isGraded C).comp G.2))
      ((counit_isGraded A).comp (F.2.comp G.2)) (counitPasteRight_restrict F G)) a
  exact ⟨by simpa only [zero_add] using! comp_mem h₁.1 h₂.1,
    by simpa only [zero_add] using! comp_mem_degree h₁.2 h₂.2⟩

theorem counitPasteRightIso_inv_isHomogeneous (F : A ⟶ C) (G : C ⟶ D) :
    (counitPasteRightIso F G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _ (counitPasteRightIso_hom_isHomogeneous F G)

end Counit
end QPiTwoEnvelope
end StringDiagrams
