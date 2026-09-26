import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-!
# Conjugate 2-morphisms: sliding lemmas and whiskering

Complements to Mathlib's `CategoryTheory.Bicategory.conjugateEquiv`. For adjunctions
`adj₁ : l₁ ⊣ r₁` and `adj₂ : l₂ ⊣ r₂` between the same objects and `α : l₂ ⟶ l₁` with
conjugate `β = conjugateEquiv adj₁ adj₂ α : r₁ ⟶ r₂`:

* `unit_comp_whiskerRight_eq`: `adj₂.unit ≫ α ▷ r₂ = adj₁.unit ≫ l₁ ◁ β` (sliding through
  the units), and `conjugateEquiv_eq_of_unit` / `conjugateEquiv_eq_iff_unit`: this equation
  characterizes the conjugate;
* `whiskerLeft_comp_counit_eq`: `r₁ ◁ α ≫ adj₁.counit = β ▷ l₂ ≫ adj₂.counit` (sliding
  through the counits);
* `conjugateEquiv_whiskerRight`, `conjugateEquiv_whiskerLeft`: conjugation with respect to
  composite adjunctions (`Adjunction.comp`) commutes with whiskering, with the order of the
  factors reversed.
-/

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

section

variable {c d : B} {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/-- Sliding a 2-morphism between left adjoints through the units: its conjugate appears on
the right adjoints. -/
theorem unit_comp_whiskerRight_eq (α : l₂ ⟶ l₁) :
    adj₂.unit ≫ α ▷ r₂ = adj₁.unit ≫ l₁ ◁ conjugateEquiv adj₁ adj₂ α := by
  rw [conjugateEquiv_apply']
  symm
  calc
    _ = 𝟙 _ ⊗≫ (adj₁.unit ▷ 𝟙 c ≫ (l₁ ≫ r₁) ◁ adj₂.unit) ⊗≫ l₁ ◁ r₁ ◁ α ▷ r₂ ⊗≫
          l₁ ◁ adj₁.counit ▷ r₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ adj₂.unit ⊗≫ (adj₁.unit ▷ (l₂ ≫ r₂) ≫ (l₁ ≫ r₁) ◁ (α ▷ r₂)) ⊗≫
          l₁ ◁ adj₁.counit ▷ r₂ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ adj₂.unit ⊗≫ α ▷ r₂ ⊗≫ leftZigzag adj₁.unit adj₁.counit ▷ r₂ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by
      rw [adj₁.left_triangle]; bicategory

/-- Sliding a 2-morphism between left adjoints through the counits: its conjugate appears
on the right adjoints. -/
theorem whiskerLeft_comp_counit_eq (α : l₂ ⟶ l₁) :
    r₁ ◁ α ≫ adj₁.counit = conjugateEquiv adj₁ adj₂ α ▷ l₂ ≫ adj₂.counit := by
  rw [conjugateEquiv_apply']
  symm
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ adj₂.unit ▷ l₂ ⊗≫ r₁ ◁ α ▷ r₂ ▷ l₂ ⊗≫
          (adj₁.counit ▷ (r₂ ≫ l₂) ≫ 𝟙 d ◁ adj₂.counit) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ adj₂.unit ▷ l₂ ⊗≫ r₁ ◁ (α ▷ (r₂ ≫ l₂) ≫ l₁ ◁ adj₂.counit) ⊗≫
          adj₁.counit := by
      rw [← whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ leftZigzag adj₂.unit adj₂.counit ⊗≫ r₁ ◁ α ⊗≫ adj₁.counit := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by
      rw [adj₂.left_triangle]; bicategory

/-- Whiskering by `l₁` after the unit of `l₁ ⊣ r₁` is injective. -/
theorem unit_comp_whiskerLeft_injective {r₂ : d ⟶ c} {β β' : r₁ ⟶ r₂}
    (h : adj₁.unit ≫ l₁ ◁ β = adj₁.unit ≫ l₁ ◁ β') : β = β' := by
  have key : ∀ γ : r₁ ⟶ r₂, γ = (ρ_ _).inv ≫ r₁ ◁ (adj₁.unit ≫ l₁ ◁ γ) ≫ (α_ _ _ _).inv ≫
      adj₁.counit ▷ r₂ ≫ (λ_ _).hom := by
    intro γ
    calc
      γ = 𝟙 _ ⊗≫ rightZigzag adj₁.unit adj₁.counit ⊗≫ γ := by
        rw [adj₁.right_triangle]; bicategory
      _ = 𝟙 _ ⊗≫ r₁ ◁ adj₁.unit ⊗≫ (adj₁.counit ▷ r₁ ≫ 𝟙 d ◁ γ) ⊗≫ 𝟙 _ := by
        bicategory
      _ = _ := by
        rw [← whisker_exchange]; bicategory
  rw [key β, key β', h]

/-- The conjugate of `α` is characterized by the unit equation. -/
theorem conjugateEquiv_eq_of_unit (α : l₂ ⟶ l₁) (β : r₁ ⟶ r₂)
    (h : adj₂.unit ≫ α ▷ r₂ = adj₁.unit ≫ l₁ ◁ β) : conjugateEquiv adj₁ adj₂ α = β :=
  unit_comp_whiskerLeft_injective adj₁ (by rw [← unit_comp_whiskerRight_eq, h])

theorem conjugateEquiv_eq_iff_unit (α : l₂ ⟶ l₁) (β : r₁ ⟶ r₂) :
    conjugateEquiv adj₁ adj₂ α = β ↔ adj₂.unit ≫ α ▷ r₂ = adj₁.unit ≫ l₁ ◁ β :=
  ⟨fun h => h ▸ unit_comp_whiskerRight_eq adj₁ adj₂ α, conjugateEquiv_eq_of_unit adj₁ adj₂ α β⟩

/-- Sliding through the units, stated for the inverse conjugate. -/
theorem unit_comp_whiskerLeft_eq (β : r₁ ⟶ r₂) :
    adj₁.unit ≫ l₁ ◁ β = adj₂.unit ≫ (conjugateEquiv adj₁ adj₂).symm β ▷ r₂ := by
  conv_lhs => rw [← Equiv.apply_symm_apply (conjugateEquiv adj₁ adj₂) β]
  rw [unit_comp_whiskerRight_eq]

/-- Sliding through the counits, stated for the inverse conjugate. -/
theorem whiskerRight_comp_counit_eq (β : r₁ ⟶ r₂) :
    β ▷ l₂ ≫ adj₂.counit = r₁ ◁ (conjugateEquiv adj₁ adj₂).symm β ≫ adj₁.counit := by
  conv_lhs => rw [← Equiv.apply_symm_apply (conjugateEquiv adj₁ adj₂) β]
  rw [whiskerLeft_comp_counit_eq]

end

section Whisker

variable {c d e : B}

/-- Conjugation with respect to composite adjunctions commutes with right whiskering of left
adjoints, which becomes left whiskering of right adjoints. -/
theorem conjugateEquiv_whiskerRight {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c} (adj₁ : l₁ ⊣ r₁)
    (adj₂ : l₂ ⊣ r₂) {f : d ⟶ e} {g : e ⟶ d} (adj : f ⊣ g) (α : l₂ ⟶ l₁) :
    conjugateEquiv (adj₁.comp adj) (adj₂.comp adj) (α ▷ f) =
      g ◁ conjugateEquiv adj₁ adj₂ α := by
  apply conjugateEquiv_eq_of_unit
  have h := unit_comp_whiskerRight_eq adj₁ adj₂ α
  dsimp only [Adjunction.comp_unit, Adjunction.compUnit]
  calc
    _ = 𝟙 _ ⊗≫ adj₂.unit ⊗≫ (l₂ ◁ adj.unit ≫ α ▷ (f ≫ g)) ▷ r₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (adj₂.unit ≫ α ▷ r₂) ⊗≫ l₁ ◁ adj.unit ▷ r₂ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ adj₁.unit ⊗≫ l₁ ◁ (𝟙 d ◁ conjugateEquiv adj₁ adj₂ α ≫ adj.unit ▷ r₂) ⊗≫
          𝟙 _ := by
      rw [h]; bicategory
    _ = _ := by
      rw [whisker_exchange]; bicategory

/-- Conjugation with respect to composite adjunctions commutes with left whiskering of left
adjoints, which becomes right whiskering of right adjoints. -/
theorem conjugateEquiv_whiskerLeft {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c} (adj₁ : l₁ ⊣ r₁)
    (adj₂ : l₂ ⊣ r₂) {f : e ⟶ c} {g : c ⟶ e} (adj : f ⊣ g) (α : l₂ ⟶ l₁) :
    conjugateEquiv (adj.comp adj₁) (adj.comp adj₂) (f ◁ α) =
      conjugateEquiv adj₁ adj₂ α ▷ g := by
  apply conjugateEquiv_eq_of_unit
  have h := unit_comp_whiskerRight_eq adj₁ adj₂ α
  dsimp only [Adjunction.comp_unit, Adjunction.compUnit]
  calc
    _ = 𝟙 _ ⊗≫ adj.unit ⊗≫ f ◁ (adj₂.unit ≫ α ▷ r₂) ▷ g ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [h]; bicategory

theorem conjugateEquiv_symm_whiskerLeft {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c} (adj₁ : l₁ ⊣ r₁)
    (adj₂ : l₂ ⊣ r₂) {f : d ⟶ e} {g : e ⟶ d} (adj : f ⊣ g) (β : r₁ ⟶ r₂) :
    (conjugateEquiv (adj₁.comp adj) (adj₂.comp adj)).symm (g ◁ β) =
      (conjugateEquiv adj₁ adj₂).symm β ▷ f := by
  rw [Equiv.symm_apply_eq, conjugateEquiv_whiskerRight, Equiv.apply_symm_apply]

theorem conjugateEquiv_symm_whiskerRight {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c} (adj₁ : l₁ ⊣ r₁)
    (adj₂ : l₂ ⊣ r₂) {f : e ⟶ c} {g : c ⟶ e} (adj : f ⊣ g) (β : r₁ ⟶ r₂) :
    (conjugateEquiv (adj.comp adj₁) (adj.comp adj₂)).symm (β ▷ g) =
      f ◁ (conjugateEquiv adj₁ adj₂).symm β := by
  rw [Equiv.symm_apply_eq, conjugateEquiv_whiskerLeft, Equiv.apply_symm_apply]

end Whisker

end StringDiagrams
