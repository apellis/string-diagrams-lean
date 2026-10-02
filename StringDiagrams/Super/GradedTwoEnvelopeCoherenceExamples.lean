import StringDiagrams.Super.GradedTwoEnvelopeCoherence
import StringDiagrams.Super.GSCat
import StringDiagrams.Super.UnitQPiEnvelope

/-!
# Concrete coherence consumer

The source 2-supercategory is `GSCat ℚ`, evaluated at the unit graded
supercategory. The probe is the invertible odd 2-morphism from the unshifted
identity to its shift `Q⁻³Π¹`. It is not an even/degree-zero replacement.
-/

noncomputable section
namespace StringDiagrams.QPiTwoEnvelope.CoherenceExamples
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

abbrev A : GSCat.{0, 0, 0} ℚ := GSCat.of ℚ (UnitSupercat ℚ)
abbrev E := QPiTwoEnvelope ℚ (GSCat.{0, 0, 0} ℚ)
abbrev a : E := ⟨⟨A⟩⟩
abbrev shifted : a ⟶ a := ⟨1, ⟨-3, 𝟙 A⟩⟩
abbrev oddShift : Jm (𝟙 A) ⟶ shifted := (shiftIso shifted).hom
abbrev identityFunctor := TwoSuperfunctor.id ℚ (GSCat.{0, 0, 0} ℚ)
abbrev identityTransformation := TwoNatTrans.id identityFunctor

/-- The actual test morphism has odd parity and negative integer degree. -/
theorem oddShift_homogeneous :
    oddShift ∈ parity (R := ℚ) _ _ 1 ∧ oddShift ∈ degree (R := ℚ) _ _ (-3) := by
  constructor
  · change 𝟙 (𝟙 A) ∈ parity (R := ℚ) _ _ (1 + (0 + 1))
    simpa only [show (1 + (0 + 1) : ZMod 2) = 0 by decide] using id_mem (R := ℚ) (𝟙 A)
  · change 𝟙 (𝟙 A) ∈ degree (R := ℚ) _ _ (-3 + (0 - -3))
    simpa only [show (-3 + (0 - -3) : ℤ) = 0 by decide] using id_mem_degree (R := ℚ) (𝟙 A)

/-- The odd negative-degree probe is nonzero over the concrete field `ℚ`. -/
theorem oddShift_ne_zero : oddShift ≠ 0 := by
  intro h
  have h' : (1 : ℚ) = 0 := congrArg
    (fun η : Jm (𝟙 A) ⟶ shifted =>
      SuperalgebraCat.toElem ((toHom η).1.app 0
        (SuperalgebraCat.star _ : UnitSupercat ℚ))) h
  exact one_ne_zero h'

/-- The original horizontal sign is genuinely negative for this pair of probes. -/
theorem oddShift_horizontal_sign :
    toHom (hcomp oddShift (shiftIso shifted).inv) =
      -hcomp (𝟙 (𝟙 A)) (𝟙 (𝟙 A)) := by
  have h := toHom_hcomp (x := oddShift) (y := (shiftIso shifted).inv)
    (id_mem (R := ℚ) (𝟙 A)) (id_mem (R := ℚ) (𝟙 A))
  change toHom (hcomp oddShift (shiftIso shifted).inv) =
    sign ℚ (1 * 0 + 0 * 1 + 1 * 1 + 0 * 1) • hcomp (𝟙 (𝟙 A)) (𝟙 (𝟙 A)) at h
  simpa using h

/-- The mapped graded transformation is tested against the odd shifted isomorphism. -/
theorem oddShift_naturality :
    (mapQPi identityFunctor).map₂ oddShift ▷ (mapQPiNatTrans identityTransformation).X a ≫
      (mapQPiNatTrans identityTransformation).x shifted =
    (mapQPiNatTrans identityTransformation).x (Jm (𝟙 A)) ≫
      (mapQPiNatTrans identityTransformation).X a ◁ (mapQPi identityFunctor).map₂ oddShift :=
  mapQPiNatTrans_naturality identityTransformation oddShift

/-- The coherence remains degree zero at the concrete odd, negatively shifted 1-morphism. -/
theorem shifted_coherence_degree :
    (mapQPiNatTrans identityTransformation).x shifted ∈ degree (R := ℚ) _ _ 0 :=
  mapQPiNatTrans_isGraded TwoNatTrans.id_isGraded shifted

/-- The transported full-record law is consumed, rather than a component projection. -/
theorem identity_whisker :
    mapQPiSupermodification (TwoNatTrans.whiskerLeft identityTransformation
      (𝟙 identityTransformation)) =
    eqToHom (mapQPiNatTrans_vcomp identityTransformation identityTransformation) ≫
      TwoNatTrans.whiskerLeft (mapQPiNatTrans identityTransformation)
        (mapQPiSupermodification (𝟙 identityTransformation)) ≫
      eqToHom (mapQPiNatTrans_vcomp identityTransformation identityTransformation).symm :=
  mapQPiSupermodification_whiskerLeft identityTransformation (𝟙 identityTransformation)

/-- The canonical inclusion square is consumed on an actual graded transformation. -/
theorem inclusion_square :
    cast (congrArg₂ (fun S T => TwoNatTrans S T)
      (twoJ_naturality identityFunctor) (twoJ_naturality identityFunctor))
      (precomposeTwoJ (mapGradedTwoNatTrans
        ⟨identityTransformation, TwoNatTrans.id_isGraded⟩).1) =
      postcomposeTwoJ identityTransformation := by
  exact congrArg Subtype.val (twoJ_naturality_gradedNatTrans
    ⟨identityTransformation, TwoNatTrans.id_isGraded⟩)

end StringDiagrams.QPiTwoEnvelope.CoherenceExamples
