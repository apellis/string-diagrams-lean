import StringDiagrams.Super.Monoidal
import StringDiagrams.Super.Graded

/-!
# Graded monoidal supercategories

The one-object case of the graded 2-supercategories of J. Brundan, A. P. Ellis, *Monoidal
supercategories*, arXiv:1603.05928v3, §6, Definition 6.2 (and its weak version): a
*graded monoidal supercategory* is a monoidal supercategory (Definition 1.4) whose underlying
supercategory is graded, such that the tensor product of morphisms adds degrees and the
coherence maps have degree `0`. In the unpacked form of `MonoidalSupercategory`: the
whiskerings preserve degrees (`StringDiagrams.GradedMonoidalSupercategory`), so that the
tensor product of homogeneous morphisms is homogeneous with degrees adding
(`GradedMonoidalSupercategory.superTensorHom_mem_degree`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory GradedSupercategory

universe w w₁ w₂

variable (R : Type w) [CommRing R] (C : Type w₁) [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [GradedSupercategory R C] [MonoidalCategoryStruct C]
  [MonoidalSupercategory R C]

/-- A graded monoidal supercategory: a monoidal supercategory whose supercategory is graded,
such that the whiskerings preserve degrees and the coherence maps have degree `0` (the
one-object case of Brundan–Ellis, Definition 6.2). -/
class GradedMonoidalSupercategory : Prop where
  whiskerLeft_mem_degree (X : C) {Y Z : C} {n : ℤ} {f : Y ⟶ Z} :
    f ∈ degree (R := R) Y Z n → X ◁ f ∈ degree (R := R) (X ⊗ Y) (X ⊗ Z) n
  whiskerRight_mem_degree {X Y : C} {n : ℤ} {f : X ⟶ Y} (Z : C) :
    f ∈ degree (R := R) X Y n → f ▷ Z ∈ degree (R := R) (X ⊗ Z) (Y ⊗ Z) n
  associator_hom_mem_degree (X Y Z : C) :
    (α_ X Y Z).hom ∈ degree (R := R) ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) 0
  leftUnitor_hom_mem_degree (X : C) : (λ_ X).hom ∈ degree (R := R) (𝟙_ C ⊗ X) X 0
  rightUnitor_hom_mem_degree (X : C) : (ρ_ X).hom ∈ degree (R := R) (X ⊗ 𝟙_ C) X 0

namespace GradedMonoidalSupercategory

variable {R C} [GradedMonoidalSupercategory R C]

omit [MonoidalSupercategory R C] in
/-- The tensor product `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)` of homogeneous morphisms is homogeneous,
with degrees adding. -/
theorem superTensorHom_mem_degree {X X' Y Y' : C} {m n : ℤ} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (hf : f ∈ degree (R := R) X X' m) (hg : g ∈ degree (R := R) Y Y' n) :
    MonoidalSupercategory.superTensorHom f g ∈ degree (R := R) (X ⊗ Y) (X' ⊗ Y') (n + m) :=
  comp_mem_degree (whiskerLeft_mem_degree X hg) (whiskerRight_mem_degree Y' hf)

theorem tensorHom_mem_degree {X X' Y Y' : C} {m n : ℤ} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (hf : f ∈ degree (R := R) X X' m) (hg : g ∈ degree (R := R) Y Y' n) :
    f ⊗ g ∈ degree (R := R) (X ⊗ Y) (X' ⊗ Y') (m + n) := by
  rw [MonoidalSupercategory.tensorHom_def (R := R)]
  exact comp_mem_degree (whiskerRight_mem_degree Y hf) (whiskerLeft_mem_degree X' hg)

end GradedMonoidalSupercategory

end StringDiagrams

end
