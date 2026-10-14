import StringDiagrams.Super.PiSOpCorrection
import StringDiagrams.Super.Bicategory

/-!
# Whiskering and the parity sign

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9: the sign of
`PiSOp.correction` changes under left and right whiskering by the coboundary of the sign
`(-1)^{ab}` (`PiSOp.correction_whiskerLeft`, `PiSOp.correction_whiskerRight`), which satisfies
the cocycle identity (`PiSOp.comparison_cocycle`).
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe r u v w

/-- Left whiskering changes the correction by the comparison-sign ratio. -/
theorem exponent_whiskerLeft (a b c p : ZMod 2) :
    exponent (a + b) (a + c) p = a * (b + c) + exponent b c p := by
  have e : (a + b) + (a + c) = b + c := by
    calc
      _ = (a + a) + (b + c) := by ac_rfl
      _ = b + c := by rw [zmod2_add_self, zero_add]
  unfold exponent
  rw [e]
  ring

/-- Right whiskering changes the correction by the other comparison-sign ratio. -/
theorem exponent_whiskerRight (a b c p : ZMod 2) :
    exponent (a + b) (c + b) p = b * (a + c) + exponent a c p := by
  have e : (a + b) + (c + b) = a + c := by
    calc
      _ = (b + b) + (a + c) := by ac_rfl
      _ = a + c := by rw [zmod2_add_self, zero_add]
  unfold exponent
  rw [e]
  ring

variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- The corrected left whiskering equation holds on every 2-morphism. -/
theorem correction_whiskerLeft (a b c : ZMod 2) {x y z : B}
    (f : x ⟶ y) {g h : y ⟶ z} (η : g ⟶ h) :
    correction (R := R) (a + b) (a + c) (f ◁ twist R a η) =
      sign R (a * (b + c)) • (f ◁ twist R a (correction (R := R) b c η)) := by
  refine induction_on (R := R) η ?_ (fun p η hη => ?_) ?_
  · have hz : f ◁ (0 : g ⟶ h) = 0 := by
      simpa only [zero_smul] using whiskerLeft_smul f (0 : R) (0 : g ⟶ h)
    simp only [map_zero, hz, smul_zero]
  · rw [twist_of_mem a hη, whiskerLeft_smul, map_smul,
      correction_of_mem (a + b) (a + c) (whiskerLeft_mem f hη),
      correction_of_mem b c hη, map_smul, twist_of_mem a hη,
      whiskerLeft_smul, whiskerLeft_smul, exponent_whiskerLeft, sign_add]
    simp only [smul_smul]
    congr 1
    ring
  · intro η θ hη hθ
    simp only [map_add, whiskerLeft_add R, hη, hθ, smul_add]

/-- The corrected right whiskering equation holds on every 2-morphism. -/
theorem correction_whiskerRight (a b c : ZMod 2) {x y z : B}
    {f g : x ⟶ y} (η : f ⟶ g) (h : y ⟶ z) :
    correction (R := R) (a + b) (c + b) (twist R b η ▷ h) =
      sign R (b * (a + c)) • (twist R b (correction (R := R) a c η) ▷ h) := by
  refine induction_on (R := R) η ?_ (fun p η hη => ?_) ?_
  · have hz : (0 : f ⟶ g) ▷ h = 0 := by
      simpa only [zero_smul] using smul_whiskerRight (0 : R) (0 : f ⟶ g) h
    simp only [map_zero, hz, smul_zero]
  · rw [twist_of_mem b hη, smul_whiskerRight, map_smul,
      correction_of_mem (a + b) (c + b) (whiskerRight_mem h hη),
      correction_of_mem a c hη, map_smul, twist_of_mem b hη,
      smul_whiskerRight, smul_whiskerRight, exponent_whiskerRight, sign_add]
    simp only [smul_smul]
    congr 1
    ring
  · intro η θ hη hθ
    simp only [map_add, add_whiskerRight R, hη, hθ, smul_add]

/-- The comparison signs satisfy the associativity cocycle identity. -/
theorem comparison_cocycle (a b c : ZMod 2) :
    sign R (b * c) * sign R (a * (b + c)) =
      sign R (a * b) * sign R ((a + b) * c) := by
  rw [← sign_add, ← sign_add]
  congr 1
  ring

/-- Both identity-comparison sign factors are one. -/
theorem comparison_units (a : ZMod 2) : sign R (0 * a) = 1 ∧ sign R (a * 0) = 1 := by
  simp
end StringDiagrams.PiSOp
