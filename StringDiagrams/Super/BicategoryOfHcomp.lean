import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Bicategories from horizontal composition

A constructor for Mathlib's `Bicategory` in terms of a horizontal composition
`hcomp : (f ⟶ g) → (h ⟶ i) → (f ≫ h ⟶ g ≫ i)` of 2-morphisms, functorial in both variables
(`hcomp_id`, `hcomp_comp`), the associator and the unitors, their naturality with respect to
`hcomp`, and the pentagon and triangle identities (`Bicategory.ofHcomp`). The whiskerings are
`f ◁ η := hcomp (𝟙 f) η` and `η ▷ h := hcomp η (𝟙 h)`, and the remaining axioms of `Bicategory`
follow. This is the bicategorical analogue of Mathlib's `MonoidalCategory.ofTensorHom`.
-/

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [CategoryStruct.{v} B] [∀ a b : B, Category.{w} (a ⟶ b)]

/-- A bicategory structure from a horizontal composition of 2-morphisms, functorial in both
variables, with associator and unitors natural with respect to it, satisfying the pentagon and
triangle identities. -/
abbrev ofHcomp
    (hcomp : ∀ {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c}, (f ⟶ g) → (h ⟶ i) → (f ≫ h ⟶ g ≫ i))
    (associator : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      (f ≫ g) ≫ h ≅ f ≫ g ≫ h)
    (leftUnitor : ∀ {a b : B} (f : a ⟶ b), 𝟙 a ≫ f ≅ f)
    (rightUnitor : ∀ {a b : B} (f : a ⟶ b), f ≫ 𝟙 b ≅ f)
    (hcomp_id : ∀ {a b c : B} (f : a ⟶ b) (h : b ⟶ c), hcomp (𝟙 f) (𝟙 h) = 𝟙 (f ≫ h))
    (hcomp_comp : ∀ {a b c : B} {f g k : a ⟶ b} {h i l : b ⟶ c} (η : f ⟶ g) (η' : g ⟶ k)
      (θ : h ⟶ i) (θ' : i ⟶ l), hcomp (η ≫ η') (θ ≫ θ') = hcomp η θ ≫ hcomp η' θ')
    (associator_naturality : ∀ {a b c d : B} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
      (η : f ⟶ f') (θ : g ⟶ g') (ι : h ⟶ h'),
      hcomp (hcomp η θ) ι ≫ (associator f' g' h').hom =
        (associator f g h).hom ≫ hcomp η (hcomp θ ι))
    (leftUnitor_naturality : ∀ {a b : B} {f f' : a ⟶ b} (η : f ⟶ f'),
      hcomp (𝟙 (𝟙 a)) η ≫ (leftUnitor f').hom = (leftUnitor f).hom ≫ η)
    (rightUnitor_naturality : ∀ {a b : B} {f f' : a ⟶ b} (η : f ⟶ f'),
      hcomp η (𝟙 (𝟙 b)) ≫ (rightUnitor f').hom = (rightUnitor f).hom ≫ η)
    (pentagon : ∀ {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
      hcomp (associator f g h).hom (𝟙 i) ≫ (associator f (g ≫ h) i).hom ≫
          hcomp (𝟙 f) (associator g h i).hom =
        (associator (f ≫ g) h i).hom ≫ (associator f g (h ≫ i)).hom)
    (triangle : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (associator f (𝟙 b) g).hom ≫ hcomp (𝟙 f) (leftUnitor g).hom =
        hcomp (rightUnitor f).hom (𝟙 g)) :
    Bicategory B where
  whiskerLeft f _ _ η := hcomp (𝟙 f) η
  whiskerRight η h := hcomp η (𝟙 h)
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft_id := hcomp_id
  whiskerLeft_comp f _ _ _ η θ := by rw [← hcomp_comp, Category.comp_id]
  id_whiskerLeft η := by
    rw [← Category.assoc, ← leftUnitor_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  comp_whiskerLeft f g _ _ η := by
    have := associator_naturality (𝟙 f) (𝟙 g) η
    rw [hcomp_id] at this
    rw [← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  id_whiskerRight := hcomp_id
  comp_whiskerRight η θ i := by rw [← hcomp_comp, Category.comp_id]
  whiskerRight_id η := by
    rw [← Category.assoc, ← rightUnitor_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  whiskerRight_comp η g h := by
    have := associator_naturality η (𝟙 g) (𝟙 h)
    rw [hcomp_id] at this
    rw [this, Iso.inv_hom_id_assoc]
  whisker_assoc f _ _ η h := by
    have := associator_naturality (𝟙 f) η (𝟙 h)
    rw [← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  whisker_exchange η θ := by
    rw [← hcomp_comp, ← hcomp_comp, Category.id_comp, Category.comp_id, Category.id_comp,
      Category.comp_id]
  pentagon := pentagon
  triangle := triangle

end Bicategory

end CategoryTheory

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

/-- The horizontal composite of 2-morphisms in a bicategory, `η ▷ h ≫ g ◁ θ : f ≫ h ⟶ g ≫ i`. -/
abbrev hcomp₂ {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i) :
    f ≫ h ⟶ g ≫ i :=
  η ▷ h ≫ g ◁ θ

theorem hcomp₂_id_id {a b c : B} (f : a ⟶ b) (h : b ⟶ c) : hcomp₂ (𝟙 f) (𝟙 h) = 𝟙 (f ≫ h) := by
  simp [hcomp₂]

theorem hcomp₂_comp {a b c : B} {f g k : a ⟶ b} {h i l : b ⟶ c} (η : f ⟶ g) (η' : g ⟶ k)
    (θ : h ⟶ i) (θ' : i ⟶ l) : hcomp₂ (η ≫ η') (θ ≫ θ') = hcomp₂ η θ ≫ hcomp₂ η' θ' := by
  simp only [hcomp₂, comp_whiskerRight, Bicategory.whiskerLeft_comp, Category.assoc]
  rw [whisker_exchange_assoc]

/-- The naturality of the associator with respect to horizontal composition. -/
theorem hcomp₂_hcomp₂_associator {a b c d : B} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (ι : h ⟶ h') :
    hcomp₂ (hcomp₂ η θ) ι ≫ (α_ f' g' h').hom = (α_ f g h).hom ≫ hcomp₂ η (hcomp₂ θ ι) := by
  simp only [hcomp₂, comp_whiskerRight, Bicategory.whiskerLeft_comp, Category.assoc]
  rw [associator_naturality_right, associator_naturality_middle_assoc,
    associator_naturality_left_assoc]

theorem hcomp₂_hcomp₂_associator_inv {a b c d : B} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (ι : h ⟶ h') :
    hcomp₂ η (hcomp₂ θ ι) ≫ (α_ f' g' h').inv = (α_ f g h).inv ≫ hcomp₂ (hcomp₂ η θ) ι := by
  rw [Iso.comp_inv_eq, Category.assoc, hcomp₂_hcomp₂_associator, Iso.inv_hom_id_assoc]

theorem hcomp₂_id_left {a b c : B} (f : a ⟶ b) {h i : b ⟶ c} (θ : h ⟶ i) :
    hcomp₂ (𝟙 f) θ = f ◁ θ := by
  simp [hcomp₂]

theorem hcomp₂_id_right {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    hcomp₂ η (𝟙 h) = η ▷ h := by
  simp [hcomp₂]

end StringDiagrams
