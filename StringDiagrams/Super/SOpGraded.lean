import StringDiagrams.Super.SOp
import StringDiagrams.Super.Graded

/-!
# The grading of the super-opposite

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9 (before Lemma
9.1): for a graded supercategory `𝒜`, the super-opposite `𝒜^{sop}` of Definition 3.4 is a graded
supercategory with the same grading, `deg(f^{sop}) = deg(f)` (`SOp.gradedSupercategory`).
-/

noncomputable section
namespace StringDiagrams.SOp
open CategoryTheory Supercategory GradedSupercategory
universe w u v
variable {R : Type w} [CommRing R] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C]

/-- The existing unsop map is a linear equivalence of morphism modules. -/
def unsopEquiv (X Y : SOp R C) : (X ⟶ Y) ≃ₗ[R] (Y.unop ⟶ X.unop) where
  toLinearMap := unsopₗ X Y
  invFun := mk'
  left_inv _ := rfl
  right_inv _ := rfl

omit [GradedSupercategory R C] in
/-- Parity projections commute with `unsop`. -/
theorem unsop_proj (p : ZMod 2) {X Y : SOp R C} (f : X ⟶ Y) :
    unsop (proj R p f) = proj R p (unsop f) := by
  refine Supercategory.induction_on (R := R) f ?_ (fun q g hg => ?_) ?_
  · simp
  · by_cases h : q = p
    · subst h
      rw [proj_of_mem hg, proj_of_mem (mem_parity_iff.mp hg)]
    · rw [proj_of_mem_ne hg h, unsop_zero, proj_of_mem_ne (mem_parity_iff.mp hg) h]
  · intro g h hg hh
    rw [map_add, unsop_add, unsop_add, map_add, hg, hh]

/-- The grading of `𝒜^{sop}` is that of `𝒜`, `deg(f^{sop}) = deg(f)`. -/
instance gradedSupercategory : GradedSupercategory R (SOp R C) where
  degree X Y n := (degree (R := R) Y.unop X.unop n).comap (unsopₗ X Y)
  isInternal_degree X Y := by
    let e := (Submodule.orderIsoMapComap (unsopEquiv X Y)).symm
    have h := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      (isInternal_degree (R := R) Y.unop X.unop)
    apply (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    refine ⟨h.1.map_orderIso e, ?_⟩
    change (⨆ n, e (degree (R := R) Y.unop X.unop n)) = ⊤
    rw [← e.map_iSup, h.2, e.map_top]
  proj_mem_degree {X Y n f} p hf := by
    change unsop (proj R p f) ∈ degree (R := R) Y.unop X.unop n
    rw [unsop_proj]
    exact proj_mem_degree p hf
  id_mem_degree X := id_mem_degree X.unop
  comp_mem_degree {X Y Z m n f g} hf hg := by
    change compC (R := R) (unsop f) (unsop g) ∈ degree (R := R) Z.unop X.unop (m + n)
    unfold compC
    rw [add_comm m n]
    exact Submodule.add_mem _ (comp_mem_degree (proj_mem_degree 0 hg) hf)
      (comp_mem_degree (proj_mem_degree 1 hg) (twist_mem_degree 1 hf))

end StringDiagrams.SOp
