import StringDiagrams.Super.PiSOpTwoNaturality
import StringDiagrams.Super.TwoFunctor

/-!
# The Π-envelope of a 2-super-opposite: coherence

Compatibility of the comparison `(-1)^{ab}` of `(𝔅^{sop})_π → (𝔅_π)^{sop}` (J. Brundan,
A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9) with associators and
unitors.
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe r u v w
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- The hom bridge sends the inverse associator to the inverse associator. -/
theorem hom_associator_inv {a b c d : TwoEnvelope R (TwoSOp R B)}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (hom a d).map (associator f g h).inv =
      (associator ((hom a b).obj f) ((hom b c).obj g) ((hom c d).obj h)).inv := by
  apply SOp.hom_ext
  apply Envelope.hom_ext
  change correction (R := R) (f.par + (g.par + h.par)) ((f.par + g.par) + h.par)
      (associator (SOp.unop f.obj) (SOp.unop g.obj) (SOp.unop h.obj)).hom = _
  rw [add_assoc]
  simp only [correction, zmod2_add_self, mul_zero, sign_zero, twist_zero, one_smul]
  rfl

/-- The hom bridge sends the left unitor to the left unitor. -/
theorem hom_leftUnitor {a b : TwoEnvelope R (TwoSOp R B)} (f : a ⟶ b) :
    (hom a b).map (leftUnitor f).hom = (leftUnitor ((hom a b).obj f)).hom := by
  apply SOp.hom_ext
  apply Envelope.hom_ext
  change correction (R := R) (0 + f.par) f.par (leftUnitor (SOp.unop f.obj)).inv = _
  simp only [zero_add, correction, zmod2_add_self, mul_zero, sign_zero, twist_zero, one_smul]
  rfl

/-- The hom bridge sends the right unitor to the right unitor. -/
theorem hom_rightUnitor {a b : TwoEnvelope R (TwoSOp R B)} (f : a ⟶ b) :
    (hom a b).map (rightUnitor f).hom = (rightUnitor ((hom a b).obj f)).hom := by
  apply SOp.hom_ext
  apply Envelope.hom_ext
  change correction (R := R) (f.par + 0) f.par (rightUnitor (SOp.unop f.obj)).inv = _
  simp only [add_zero, correction, zmod2_add_self, mul_zero, sign_zero, twist_zero, one_smul]
  rfl

/-- The complete associator diagram, with both nontrivial comparison factors. -/
theorem comparison_associator {a b c d : TwoEnvelope R (TwoSOp R B)}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (hom a b).obj f ◁ (comparison g h).hom ≫ (comparison f (g ≫ h)).hom ≫
        (hom a d).map (associator f g h).inv =
      (associator ((hom a b).obj f) ((hom b c).obj g) ((hom c d).obj h)).inv ≫
        (comparison f g).hom ▷ (hom c d).obj h ≫ (comparison (f ≫ g) h).hom := by
  change (hom a b).obj f ◁ (sign R (g.par * h.par) • 𝟙 _) ≫
      (sign R (f.par * (g.par + h.par)) • 𝟙 _) ≫ _ =
    _ ≫ (sign R (f.par * g.par) • 𝟙 _) ▷ (hom c d).obj h ≫
      (sign R ((f.par + g.par) * h.par) • 𝟙 _)
  erw [whiskerLeft_smul, whiskerLeft_id (R := R), smul_whiskerRight, id_whiskerRight (R := R),
    Linear.smul_comp, Category.id_comp, Linear.smul_comp, Category.id_comp,
    Linear.comp_smul, Category.comp_id, Linear.comp_smul, Linear.comp_smul, Category.comp_id]
  erw [hom_associator_inv, smul_smul, smul_smul, comparison_cocycle, mul_comm]

/-- The left-unit coherence diagram. -/
theorem comparison_leftUnitor {a b : TwoEnvelope R (TwoSOp R B)} (f : a ⟶ b) :
    (identityComparison a).hom ▷ (hom a b).obj f ≫ (comparison (𝟙 a) f).hom ≫
        (hom a b).map (leftUnitor f).hom = (leftUnitor ((hom a b).obj f)).hom := by
  change 𝟙 _ ▷ (hom a b).obj f ≫ (sign R (0 * f.par) • 𝟙 _) ≫ _ = _
  erw [zero_mul, sign_zero, one_smul, id_whiskerRight (R := R),
    Category.id_comp, Category.id_comp]
  exact hom_leftUnitor f

/-- The right-unit coherence diagram. -/
theorem comparison_rightUnitor {a b : TwoEnvelope R (TwoSOp R B)} (f : a ⟶ b) :
    (hom a b).obj f ◁ (identityComparison b).hom ≫ (comparison f (𝟙 b)).hom ≫
        (hom a b).map (rightUnitor f).hom = (rightUnitor ((hom a b).obj f)).hom := by
  change (hom a b).obj f ◁ 𝟙 _ ≫ (sign R (f.par * 0) • 𝟙 _) ≫ _ = _
  erw [mul_zero, sign_zero, one_smul, whiskerLeft_id (R := R),
    Category.id_comp, Category.id_comp]
  exact hom_rightUnitor f
end StringDiagrams.PiSOp
