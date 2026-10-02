import StringDiagrams.Super.GradedTwoEnvelopeCounitCoherence
import StringDiagrams.Super.GradedTwoEnvelopeCounitExamples

/-!
# Counit inverse laws on the nonzero odd degree -3 fixture over ℚ

The cancellation maps are actual supermodifications in the same concrete
envelope as the odd shifted isomorphism. Their parity and degree, and both
composite inverse laws for the non-strict inclusion square, are consumed.
-/

noncomputable section
namespace StringDiagrams.QPiTwoEnvelope.CounitCoherenceExamples
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
open CoherenceExamples CounitExamples

set_option backward.isDefEq.respectTransparency false

abbrev triangleCancellation := counitLeftTriangleCompInvIso base

/-- Retain the original nonzero odd negative-degree fixture while consuming
both directions of the actual cancellation modification below. -/
theorem odd_probe :
    oddShift ≠ 0 ∧ oddShift ∈ parity (R := ℚ) _ _ 1 ∧
      oddShift ∈ degree (R := ℚ) _ _ (-3) :=
  ⟨oddShift_ne_zero, oddShift_homogeneous⟩

/-- Both directions of the triangle cancellation retain parity and degree. -/
theorem triangle_cancellation_homogeneous :
    triangleCancellation.hom.IsHomogeneous 0 0 ∧
    triangleCancellation.inv.IsHomogeneous 0 0 :=
  ⟨counitLeftTriangleCompInvIso_hom_isHomogeneous base,
    counitLeftTriangleCompInvIso_inv_isHomogeneous base⟩

/-- The non-strict inclusion square also has an actual inverse law. -/
theorem inclusion_cancellation_inverse_laws :
    (counitNaturalityCompInvIso inclusion).hom ≫ (counitNaturalityCompInvIso inclusion).inv =
      𝟙 (TwoNatTrans.vcomp (counitNaturality inclusion) (counitNaturalityInv inclusion)) ∧
    (counitNaturalityInvCompIso inclusion).hom ≫ (counitNaturalityInvCompIso inclusion).inv =
      𝟙 (TwoNatTrans.vcomp (counitNaturalityInv inclusion) (counitNaturality inclusion)) :=
  ⟨(counitNaturalityCompInvIso inclusion).hom_inv_id,
    (counitNaturalityInvCompIso inclusion).hom_inv_id⟩

end StringDiagrams.QPiTwoEnvelope.CounitCoherenceExamples
