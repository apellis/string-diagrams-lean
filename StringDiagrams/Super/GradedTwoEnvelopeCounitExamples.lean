import StringDiagrams.Super.GradedTwoEnvelopeCounit
import StringDiagrams.Super.GradedTwoEnvelopeCoherenceExamples

/-!
# Evaluation on the concrete field fixture

The original nonzero odd degree `-3` probe is evaluated back unchanged. A
nontrivial doubly shifted 1-morphism is evaluated using the chosen shifts,
not by throwing away its labels. The final example detects failure of
strict counit naturality by its parity label.
-/

noncomputable section
namespace StringDiagrams.QPiTwoEnvelope.CounitExamples
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
open CoherenceExamples

abbrev base : GTwoSCat ℚ := GTwoSCat.of ℚ (GSCat.{0, 0, 0} ℚ)
abbrev target : QPiTwoGSCat ℚ := GTwoSCat.envelope.obj base
abbrev ε := counit target

/-- Evaluation really handles nontrivial formal Q and Π shifts. -/
theorem evaluate_shifts :
    ε.map (⟨1, ⟨1, shifted⟩⟩ : (⟨⟨a⟩⟩ : QPiTwoEnvelope ℚ E) ⟶ ⟨⟨a⟩⟩) =
      (shifted ≫ QPiTwoSupercategory.q (R := ℚ) a) ≫ PiTwoSupercategory.pi (R := ℚ) a :=
  counit_map_one_one target shifted

/-- The odd degree -3 morphism is not replaced by an even or zero probe. -/
theorem evaluate_oddShift : ε.map₂ (J2 oddShift) = oddShift :=
  extendQPi_map₂_J _ _

theorem evaluate_oddShift_nonzero : ε.map₂ (J2 oddShift) ≠ 0 := by
  rw [evaluate_oddShift]
  exact oddShift_ne_zero

theorem evaluate_oddShift_homogeneous :
    ε.map₂ (J2 oddShift) ∈ parity (R := ℚ) _ _ 1 ∧
    ε.map₂ (J2 oddShift) ∈ degree (R := ℚ) _ _ (-3) := by
  rw [evaluate_oddShift]
  exact oddShift_homogeneous

/-- Naturality is tested with an actual graded functor, not just the identity. -/
abbrev inclusion : target ⟶ GTwoSCat.envelope.obj target.toGTwoSCat :=
  ⟨twoJ ℚ target, twoJ_isGraded (R := ℚ) (B := target)⟩

/-- The two legs have an actual strong graded comparison. -/
theorem inclusion_comparison :
    (counitNaturality inclusion).IsStrong ∧ (counitNaturality inclusion).IsGraded :=
  ⟨counitNaturality_isStrong inclusion, counitNaturality_isGraded inclusion⟩

/-- The counit square cannot be replaced by strict equality: one leg retains
an outer Π label and the other includes the evaluated result with label zero. -/
theorem counit_naturality_not_strict :
    (mapQPi inclusion.1).comp (counit (GTwoSCat.envelope.obj target.toGTwoSCat)) ≠
      (counit target).comp inclusion.1 := by
  intro h
  have hmap := congrArg (fun F =>
    (F.map (⟨1, ⟨1, shifted⟩⟩ : (⟨⟨a⟩⟩ : QPiTwoEnvelope ℚ E) ⟶ ⟨⟨a⟩⟩)).par) h
  have bad : (1 : ZMod 2) = 0 := hmap
  exact one_ne_zero bad

end StringDiagrams.QPiTwoEnvelope.CounitExamples
