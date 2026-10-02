import StringDiagrams.Super.GradedTwoEnvelopeCounitRightLegAssembly

/-!
# The actual full counit paste compared with the direct square

The original transported, functor-whiskered legs are identified with their
chosen density comparisons, then composed by `comparisonCompIso`. The source,
middle, and target transports in `counitNaturalityPaste` are retained through
the published leg identifications. Only proofs of the same restriction equality
are identified at the final endpoint; equality of the envelope functors is
neither assumed nor inferred. No strict counit naturality, global graded
2-adjunction, or triangle coherence is asserted.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁
variable {R : Type w} [CommRing R]
namespace QPiTwoEnvelope
set_option backward.isDefEq.respectTransparency false
variable {B C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) (G : C ⟶ D)

/-- The composite of the two restriction paths has precisely the direct path's
endpoints. Proof irrelevance changes no functor or transformation data. -/
theorem counitPaste_restrict_trans :
    (counitPasteLeft_restrict F G).trans (counitPasteRight_restrict F G) =
      counit_naturality_restrict (F ≫ G) := rfl

/-- Composition of the original chosen leg comparisons lands at the original
direct counit comparison. The common-extension transports remain in
`comparisonCompIso`; its last restriction proof agrees by proof irrelevance. -/
def counitPasteComparisonsIso :
    TwoNatTrans.vcomp (counitPasteLeftComparison F G) (counitPasteRightComparison F G) ≅
      counitNaturality (F ≫ G) :=
  comparisonCompIso _ _ _
    ((mapQPi_isGraded (F ≫ G).2).comp (counit_isGraded D))
    ((mapQPi_isGraded F.2).comp ((counit_isGraded C).comp G.2))
    ((counit_isGraded B).comp (F.2.comp G.2))
    (counitPasteLeft_restrict F G) (counitPasteRight_restrict F G)

theorem counitPasteComparisonsIso_hom_isHomogeneous :
    (counitPasteComparisonsIso F G).hom.IsHomogeneous 0 0 :=
  comparisonCompIso_hom_isHomogeneous _ _ _ _ _ _ _ _

/-- The genuine full paste-to-direct modification for arbitrary graded bundled
functors. Both original functor-whiskered legs, including the postcomposition
compositors, occur in the source. -/
def counitNaturalityPasteIso :
    counitNaturalityPaste F G ≅ counitNaturality (F ≫ G) :=
  TwoSupercategory.whiskerRightIso (R := R)
    (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
    (counitPasteLeftIso F G) (counitPasteRight F G) ≪≫
  TwoSupercategory.whiskerLeftIso (R := R)
    (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
    (counitPasteLeftComparison F G) (counitPasteRightIso F G) ≪≫
  counitPasteComparisonsIso F G

set_option maxHeartbeats 800000 in
theorem counitNaturalityPasteIso_hom_isHomogeneous :
    (counitNaturalityPasteIso F G).hom.IsHomogeneous 0 0 := by
  intro a
  have hl := counitPasteLeftIso_hom_isHomogeneous F G a
  have hr := counitPasteRightIso_hom_isHomogeneous F G a
  have hc := counitPasteComparisonsIso_hom_isHomogeneous F G a
  constructor
  · simpa only [zero_add] using! comp_mem
      (whiskerRight_mem ((counitPasteRight F G).X a) hl.1)
      (comp_mem (whiskerLeft_mem ((counitPasteLeftComparison F G).X a) hr.1) hc.1)
  · simpa only [zero_add] using! comp_mem_degree
      (GradedTwoSupercategory.whiskerRight_mem_degree ((counitPasteRight F G).X a) hl.2)
      (comp_mem_degree
        (GradedTwoSupercategory.whiskerLeft_mem_degree ((counitPasteLeftComparison F G).X a) hr.2)
        hc.2)

theorem counitNaturalityPasteIso_inv_isHomogeneous :
    (counitNaturalityPasteIso F G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _ (counitNaturalityPasteIso_hom_isHomogeneous F G)

end QPiTwoEnvelope
end StringDiagrams
