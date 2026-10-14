import StringDiagrams.Super.TwoSOpLaws

/-!
# Horizontal composition in the 2-super-opposite

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 3.4:
horizontal composition of 2-morphisms in `𝔄^{sop}` is horizontal composition in `𝔄`,
`x^{sop} y^{sop} = (xy)^{sop}` (`TwoSOp.unsop_hcomp`; the Koszul sign of the vertical
composition cancels the sign of the super interchange law), and the vertical composite of two
odd 2-morphisms acquires a sign (`TwoSOp.unsop_comp_odd`).
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
universe r u v w
namespace TwoSOp
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

private theorem horizontal_compC {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c}
    (η : g ⟶ f) (θ : i ⟶ h) :
    SOp.compC (R := R) (η ▷ h) (g ◁ θ) = η ▷ i ≫ f ◁ θ := by
  refine induction_on (R := R) η ?_ (fun p η hη => ?_) ?_
  · simp only [zero_whiskerRight R, SOp.zero_compC, Limits.zero_comp]
  · refine induction_on (R := R) θ ?_ (fun q θ hθ => ?_) ?_
    · simp only [whiskerLeft_zero R, SOp.compC_zero, Limits.comp_zero]
    · rw [SOp.compC_of_mem (whiskerRight_mem h hη) (whiskerLeft_mem g hθ)]
      exact ((super_interchange hη hθ).trans (koszulSign_smul p q _)).symm
    · intro θ θ' hθ hθ'
      rw [whiskerLeft_add (R := R), SOp.compC_add, whiskerLeft_add (R := R),
        Preadditive.comp_add, hθ, hθ']
  · intro η η' hη hη'
    rw [add_whiskerRight (R := R), SOp.add_compC, add_whiskerRight (R := R),
      Preadditive.add_comp, hη, hη']

/-- Horizontal composition in `𝔄^{sop}` is horizontal composition in `𝔄` after `unsop`.
The proof uses Koszul cancellation, not definitional equality. -/
theorem unsop_hcomp {a b c : TwoSOp R B} {f g : a ⟶ b} {h i : b ⟶ c}
    (η : f ⟶ g) (θ : h ⟶ i) :
    SOp.unsop (hcomp η θ) = hcomp (SOp.unsop η) (SOp.unsop θ) := by
  change SOp.compC (R := R) (SOp.unsop η ▷ SOp.unop h) (SOp.unop g ◁ SOp.unsop θ) =
    SOp.unsop η ▷ SOp.unop i ≫ SOp.unop f ◁ SOp.unsop θ
  exact horizontal_compC _ _

/-- The vertical odd/odd composite retains its minus sign. -/
theorem unsop_comp_odd {a b : TwoSOp R B} {f g h : a ⟶ b} {η : f ⟶ g} {θ : g ⟶ h}
    (hη : η ∈ parity (R := R) f g 1) (hθ : θ ∈ parity (R := R) g h 1) :
    SOp.unsop (η ≫ θ) = -(SOp.unsop θ ≫ SOp.unsop η) := by
  change SOp.unsop η ∈ parity (R := R) (SOp.unop g) (SOp.unop f) 1 at hη
  change SOp.unsop θ ∈ parity (R := R) (SOp.unop h) (SOp.unop g) 1 at hθ
  change SOp.compC (R := R) (SOp.unsop η) (SOp.unsop θ) = _
  rw [SOp.compC_of_mem hη hθ, mul_one, sign_one, neg_one_smul]
end TwoSOp
end StringDiagrams
