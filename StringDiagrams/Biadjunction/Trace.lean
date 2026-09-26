import StringDiagrams.Biadjunction.Cyclic

/-!
# Traces for biadjunctions

For a biadjunction `P : f ⊣⊢ g` with `f : a ⟶ b` and `α : f ⟶ f`, the right trace
`rightTrace P α : 𝟙 a ⟶ 𝟙 a` closes the strand of `α` on its right and the left trace
`leftTrace P α : 𝟙 b ⟶ 𝟙 b` closes it on its left (the conventions of Etingof–Gelaki–
Nikshych–Ostrik, *Tensor categories*, §4.7, with `f ≫ g` drawn as `f` to the left of `g`).
Traces of identities are the dimensions ("bubbles").

## Main results

* `rightTrace_comp`: for `α : f ⟶ f'` and `β : f' ⟶ f`,
  `rightTrace P (α ≫ β) = rightTrace P' (β ≫ doubleMate P P' α)`, with no hypothesis; hence
  `rightTrace P (α ≫ β) = rightTrace P' (β ≫ α)` as soon as *one* of `α`, `β` is cyclic
  (`rightTrace_comp_comm_of_isCyclic_left`, `rightTrace_comp_comm_of_isCyclic_right`).
  Similarly `leftTrace_comp` and its corollaries.
* Traces and mates: `rightTrace P α = leftTrace P.symm (rightMate P P α)
  = leftTrace P.symm (leftMate P P α)`, and
  `leftTrace P α = rightTrace P.symm (rightMate P P α) = rightTrace P.symm (leftMate P P α)`;
  no cyclicity is needed. Consequently, for cyclic `α` the right trace of `α` is the left trace
  of its (unique) mate.
* `rightTrace_comp_hcomp`, `leftTrace_comp_hcomp` (and the whiskered special cases): traces
  for composite biadjunctions are computed strand by strand, the inner closed strand becoming
  a trace (a bubble) in the region it encloses.

Without cyclicity, `rightTrace P (α ≫ β)` and `rightTrace P' (β ≫ α)` need not agree, and
the left and right traces of `α` need not agree (no sphericality is assumed or implied).
-/

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

namespace Biadjunction

variable {a b c : B} {f f' : a ⟶ b} {g g' : b ⟶ a}

theorem rightTrace_id (P : f ⊣⊢ g) : rightTrace P (𝟙 f) = P.left.unit ≫ P.right.counit := by
  simp [rightTrace]

theorem leftTrace_id (P : f ⊣⊢ g) : leftTrace P (𝟙 f) = P.right.unit ≫ P.left.counit := by
  simp [leftTrace]

theorem leftTrace_symm (P : f ⊣⊢ g) (γ : g ⟶ g) :
    leftTrace P.symm γ = P.left.unit ≫ f ◁ γ ≫ P.right.counit := rfl

theorem rightTrace_symm (P : f ⊣⊢ g) (γ : g ⟶ g) :
    rightTrace P.symm γ = P.right.unit ≫ γ ▷ f ≫ P.left.counit := rfl

/-- Cyclicity of the right trace up to a full rotation, with no hypothesis. -/
theorem rightTrace_comp (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') (β : f' ⟶ f) :
    rightTrace P (α ≫ β) = rightTrace P' (β ≫ doubleMate P P' α) := by
  have h₁ : P.left.unit ≫ α ▷ g = P'.left.unit ≫ f' ◁ rightMate P P' α :=
    unit_comp_whiskerRight_eq P'.left P.left α
  have h₂ : f ◁ rightMate P P' α ≫ P.right.counit =
      doubleMate P P' α ▷ g' ≫ P'.right.counit :=
    whiskerLeft_comp_counit_eq P.right P'.right (rightMate P P' α)
  simp only [rightTrace, comp_whiskerRight, Category.assoc]
  rw [reassoc_of% h₁, whisker_exchange_assoc, h₂]

/-- Cyclicity of the left trace up to a full rotation, with no hypothesis. -/
theorem leftTrace_comp (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') (β : f' ⟶ f) :
    leftTrace P (α ≫ β) = leftTrace P' (doubleMate P' P β ≫ α) := by
  have h₁ : g ◁ β ≫ P.left.counit = rightMate P' P β ▷ f' ≫ P'.left.counit :=
    whiskerLeft_comp_counit_eq P.left P'.left β
  have h₂ : P.right.unit ≫ rightMate P' P β ▷ f =
      P'.right.unit ≫ g' ◁ doubleMate P' P β :=
    unit_comp_whiskerRight_eq P'.right P.right (rightMate P' P β)
  simp only [leftTrace, Bicategory.whiskerLeft_comp, Category.assoc]
  rw [h₁, whisker_exchange_assoc, reassoc_of% h₂]

theorem rightTrace_comp_comm_of_isCyclic_left {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (hα : IsCyclic P P' α) (β : f' ⟶ f) :
    rightTrace P (α ≫ β) = rightTrace P' (β ≫ α) := by
  rw [rightTrace_comp P P', hα.doubleMate_eq]

theorem rightTrace_comp_comm_of_isCyclic_right {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} (α : f ⟶ f')
    {β : f' ⟶ f} (hβ : IsCyclic P' P β) :
    rightTrace P (α ≫ β) = rightTrace P' (β ≫ α) := by
  rw [rightTrace_comp P' P, hβ.doubleMate_eq]

theorem leftTrace_comp_comm_of_isCyclic_right {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} (α : f ⟶ f')
    {β : f' ⟶ f} (hβ : IsCyclic P' P β) :
    leftTrace P (α ≫ β) = leftTrace P' (β ≫ α) := by
  rw [leftTrace_comp P P', hβ.doubleMate_eq]

theorem leftTrace_comp_comm_of_isCyclic_left {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (hα : IsCyclic P P' α) (β : f' ⟶ f) :
    leftTrace P (α ≫ β) = leftTrace P' (β ≫ α) := by
  rw [leftTrace_comp P' P, hα.doubleMate_eq]

/-- The right trace of `α` is the left trace of its right mate. -/
theorem rightTrace_eq_leftTrace_rightMate (P : f ⊣⊢ g) (α : f ⟶ f) :
    rightTrace P α = leftTrace P.symm (rightMate P P α) := by
  rw [rightTrace, leftTrace_symm, reassoc_of% (unit_comp_whiskerRight_eq P.left P.left α)]
  rfl

/-- The right trace of `α` is the left trace of its left mate. -/
theorem rightTrace_eq_leftTrace_leftMate (P : f ⊣⊢ g) (α : f ⟶ f) :
    rightTrace P α = leftTrace P.symm (leftMate P P α) := by
  rw [rightTrace, leftTrace_symm, whiskerRight_comp_counit_eq P.right P.right α]
  rfl

/-- The left trace of `α` is the right trace of its right mate. -/
theorem leftTrace_eq_rightTrace_rightMate (P : f ⊣⊢ g) (α : f ⟶ f) :
    leftTrace P α = rightTrace P.symm (rightMate P P α) := by
  rw [leftTrace, rightTrace_symm, whiskerLeft_comp_counit_eq P.left P.left α]
  rfl

/-- The left trace of `α` is the right trace of its left mate. -/
theorem leftTrace_eq_rightTrace_leftMate (P : f ⊣⊢ g) (α : f ⟶ f) :
    leftTrace P α = rightTrace P.symm (leftMate P P α) := by
  rw [leftTrace, rightTrace_symm, reassoc_of% (unit_comp_whiskerLeft_eq P.right P.right α)]
  rfl

/-- The right trace of a 2-morphism `γ : g ⟶ g` for the exchanged biadjunction is the left
trace of either of its inverse mates. -/
theorem rightTrace_symm_eq_leftTrace (P : f ⊣⊢ g) (γ : g ⟶ g) :
    rightTrace P.symm γ = leftTrace P ((rightMate P P).symm γ) := by
  rw [leftTrace_eq_rightTrace_rightMate, Equiv.apply_symm_apply]

theorem leftTrace_symm_eq_rightTrace (P : f ⊣⊢ g) (γ : g ⟶ g) :
    leftTrace P.symm γ = rightTrace P ((rightMate P P).symm γ) := by
  rw [rightTrace_eq_leftTrace_rightMate, Equiv.apply_symm_apply]

/-! ## Partial traces -/

section Partial

variable {h : b ⟶ c} {k : c ⟶ b}

/-- The right trace for a composite biadjunction, of `γ ▷ h ≫ f ◁ β`: the inner `h`-strand
closes to the right trace of `β`, inside the `f`-strand. -/
theorem rightTrace_comp_hcomp (P : f ⊣⊢ g) (R : h ⊣⊢ k) (γ : f ⟶ f) (β : h ⟶ h) :
    rightTrace (P.comp R) (γ ▷ h ≫ f ◁ β) =
      rightTrace P (γ ≫ (ρ_ f).inv ≫ f ◁ rightTrace R β ≫ (ρ_ f).hom) := by
  simp only [rightTrace, comp_left, comp_right, Adjunction.comp_unit, Adjunction.comp_counit,
    Adjunction.compUnit, Adjunction.compCounit]
  calc
    _ = P.left.unit ⊗≫ (f ◁ R.left.unit ≫ γ ▷ (h ≫ k)) ▷ g ⊗≫ f ◁ β ▷ k ▷ g ⊗≫
          f ◁ R.right.counit ▷ g ⊗≫ P.right.counit := by
      bicategory
    _ = P.left.unit ⊗≫ (γ ▷ 𝟙 b ≫ f ◁ R.left.unit) ▷ g ⊗≫ f ◁ β ▷ k ▷ g ⊗≫
          f ◁ R.right.counit ▷ g ⊗≫ P.right.counit := by
      rw [whisker_exchange]
    _ = _ := by
      bicategory

/-- The left trace for a composite biadjunction, of `γ ▷ h ≫ f ◁ β`: the inner `f`-strand
closes to the left trace of `γ`, inside the `h`-strand. -/
theorem leftTrace_comp_hcomp (P : f ⊣⊢ g) (R : h ⊣⊢ k) (γ : f ⟶ f) (β : h ⟶ h) :
    leftTrace (P.comp R) (γ ▷ h ≫ f ◁ β) =
      leftTrace R ((λ_ h).inv ≫ leftTrace P γ ▷ h ≫ (λ_ h).hom ≫ β) := by
  simp only [leftTrace, comp_left, comp_right, Adjunction.comp_unit, Adjunction.comp_counit,
    Adjunction.compUnit, Adjunction.compCounit]
  calc
    _ = R.right.unit ⊗≫ k ◁ P.right.unit ▷ h ⊗≫ k ◁ g ◁ γ ▷ h ⊗≫
          k ◁ ((g ≫ f) ◁ β ≫ P.left.counit ▷ h) ⊗≫ R.left.counit := by
      bicategory
    _ = R.right.unit ⊗≫ k ◁ P.right.unit ▷ h ⊗≫ k ◁ g ◁ γ ▷ h ⊗≫
          k ◁ (P.left.counit ▷ h ≫ 𝟙 b ◁ β) ⊗≫ R.left.counit := by
      rw [whisker_exchange]
    _ = _ := by
      bicategory

theorem rightTrace_comp_whiskerRight (P : f ⊣⊢ g) (R : h ⊣⊢ k) (γ : f ⟶ f) :
    rightTrace (P.comp R) (γ ▷ h) =
      rightTrace P (γ ≫ (ρ_ f).inv ≫ f ◁ rightTrace R (𝟙 h) ≫ (ρ_ f).hom) := by
  rw [← rightTrace_comp_hcomp, Bicategory.whiskerLeft_id, Category.comp_id]

theorem rightTrace_comp_whiskerLeft (P : f ⊣⊢ g) (R : h ⊣⊢ k) (β : h ⟶ h) :
    rightTrace (P.comp R) (f ◁ β) =
      rightTrace P ((ρ_ f).inv ≫ f ◁ rightTrace R β ≫ (ρ_ f).hom) := by
  have := rightTrace_comp_hcomp P R (𝟙 f) β
  rwa [id_whiskerRight, Category.id_comp, Category.id_comp] at this

theorem leftTrace_comp_whiskerLeft (P : f ⊣⊢ g) (R : h ⊣⊢ k) (β : h ⟶ h) :
    leftTrace (P.comp R) (f ◁ β) =
      leftTrace R ((λ_ h).inv ≫ leftTrace P (𝟙 f) ▷ h ≫ (λ_ h).hom ≫ β) := by
  rw [← leftTrace_comp_hcomp, id_whiskerRight, Category.id_comp]

theorem leftTrace_comp_whiskerRight (P : f ⊣⊢ g) (R : h ⊣⊢ k) (γ : f ⟶ f) :
    leftTrace (P.comp R) (γ ▷ h) =
      leftTrace R ((λ_ h).inv ≫ leftTrace P γ ▷ h ≫ (λ_ h).hom) := by
  have := leftTrace_comp_hcomp P R γ (𝟙 h)
  rwa [Bicategory.whiskerLeft_id, Category.comp_id, Category.comp_id] at this

end Partial

end Biadjunction

end StringDiagrams
