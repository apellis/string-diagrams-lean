import StringDiagrams.Super.PiSOpBridge
import StringDiagrams.Super.PiSOpHorizontal
import StringDiagrams.Super.TwoSOpGraded
import StringDiagrams.Super.GradedTwoEnvelope

/-!
# The Π-envelope of a 2-super-opposite: data

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9 (before
Lemma 9.1): object, hom-functor and comparison data of the 2-superfunctor
`(𝔅^{sop})_π → (𝔅_π)^{sop}`. On hom categories it is `PiSOp.bridge`; its composition
comparison at `(Πᵃ F, Πᵇ G)` is `(-1)^{ab}` times the identity (`PiSOp.comparison`), and the
identity comparison is the identity.
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe r u v w

/-- A scalar-sign identity isomorphism in any linear category. -/
def signIso {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] (p : ZMod 2) (X : C) : X ≅ X where
  hom := sign R p • 𝟙 X
  inv := sign R p • 𝟙 X
  hom_inv_id := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      smul_smul, sign_mul_self, one_smul]
  inv_hom_id := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      smul_smul, sign_mul_self, one_smul]

/-- Twisting commutes with unsop, preserving parity. -/
theorem unsop_twist {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] [Supercategory R C]
    {X Y : SOp R C} (p : ZMod 2) (f : X ⟶ Y) :
    SOp.unsop (twist R p f) = twist R p (SOp.unsop f) := by
  rw [twist_apply, SOp.unsop_add, SOp.unsop_smul, SOp.unsop_proj, SOp.unsop_proj]
  rfl

variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- The bridge leaves underlying objects unchanged. -/
def obj (a : TwoEnvelope R (TwoSOp R B)) : TwoSOp R (TwoEnvelope R B) := ⟨⟨a.as.unop⟩⟩

/-- The hom functors are `PiSOp.bridge`. -/
def hom (a b : TwoEnvelope R (TwoSOp R B)) : (a ⟶ b) ⥤ (obj a ⟶ obj b) := bridge

/-- The composition comparison carries the product of the two parity tags. -/
def comparison {a b c : TwoEnvelope R (TwoSOp R B)} (f : a ⟶ b) (g : b ⟶ c) :
    (hom a b).obj f ≫ (hom b c).obj g ≅ (hom a c).obj (f ≫ g) :=
  signIso (R := R) (f.par * g.par) _

/-- The identity comparison is the identity. -/
def identityComparison (a : TwoEnvelope R (TwoSOp R B)) :
    𝟙 (obj a) ≅ (hom a a).obj (𝟙 a) := Iso.refl _

/-- The signed composition comparison is even. -/
theorem comparison_even {a b c : TwoEnvelope R (TwoSOp R B)} (f : a ⟶ b) (g : b ⟶ c) :
    (comparison f g).hom ∈ parity (R := R)
      ((hom a b).obj f ≫ (hom b c).obj g) ((hom a c).obj (f ≫ g)) 0 :=
  Submodule.smul_mem _ _ (id_mem _)

variable [∀ a b : B, GradedSupercategory R (a ⟶ b)]

/-- The signed composition comparison has total degree zero. -/
theorem comparison_degree {a b c : TwoEnvelope R (TwoSOp R B)} (f : a ⟶ b) (g : b ⟶ c) :
    (comparison f g).hom ∈ degree (R := R)
      ((hom a b).obj f ≫ (hom b c).obj g) ((hom a c).obj (f ≫ g)) 0 :=
  Submodule.smul_mem _ _ (id_mem_degree _)
end StringDiagrams.PiSOp
