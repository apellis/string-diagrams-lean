import StringDiagrams.Super.TwoSOpLaws
import StringDiagrams.Super.SOpGraded
import StringDiagrams.Super.GradedTwo

/-!
# The grading of the 2-super-opposite

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9 (before
Lemma 9.1): if `𝔄` is a graded 2-supercategory then so is `𝔄^{sop}`, with the same degrees
(`TwoSOp.gradedTwoSupercategory`, `TwoSOp.mem_degree_iff`).
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory GradedSupercategory
universe r u v w
namespace TwoSOp
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B]

instance (a b : TwoSOp R B) : GradedSupercategory R (a ⟶ b) := SOp.gradedSupercategory

instance gradedTwoSupercategory : GradedTwoSupercategory R (TwoSOp R B) where
  whiskerLeft_mem_degree f _ _ _ _ hη :=
    GradedTwoSupercategory.whiskerLeft_mem_degree (SOp.unop f) hη
  whiskerRight_mem_degree h hη :=
    GradedTwoSupercategory.whiskerRight_mem_degree (SOp.unop h) hη
  associator_hom_mem_degree f g h := GradedTwoSupercategory.associator_inv_mem_degree
    (SOp.unop f) (SOp.unop g) (SOp.unop h)
  leftUnitor_hom_mem_degree f := GradedTwoSupercategory.leftUnitor_inv_mem_degree (SOp.unop f)
  rightUnitor_hom_mem_degree f := GradedTwoSupercategory.rightUnitor_inv_mem_degree (SOp.unop f)

omit [GradedTwoSupercategory R B] in
/-- The internal integer degree is unchanged, not negated. -/
theorem mem_degree_iff {a b : TwoSOp R B} {f g : a ⟶ b} {n : ℤ} {η : f ⟶ g} :
    η ∈ degree (R := R) f g n ↔
      SOp.unsop η ∈ degree (R := R) (SOp.unop g) (SOp.unop f) n := Iff.rfl
end TwoSOp
end StringDiagrams
