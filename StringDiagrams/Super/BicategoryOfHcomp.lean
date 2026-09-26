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
def ofHcomp
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
