import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Logic.Equiv.Prod

/-!
# Monoidal structures on the additive envelope and the idempotent completion

For a monoidal preadditive category `D`, the additive envelope `Mat_ D` is monoidal with
`(Xᵢ)ᵢ ⊗ (Yⱼ)ⱼ = (Xᵢ ⊗ Yⱼ)_{(i, j)}` and the tensor product of matrices computed entrywise
(`Mat_.instMonoidalCategory`), and the idempotent completion `Karoubi D` of a monoidal category
is monoidal with `(X, p) ⊗ (Y, q) = (X ⊗ Y, p ⊗ q)` (`Karoubi.instMonoidalCategory`). Both are
monoidal preadditive (and monoidal linear), and the embeddings are compatible with the tensor
products (`Mat_.embeddingTensorIso`, `Karoubi.toKaroubiTensorIso`).

These are the monoidal structures on the additive Karoubi envelope used in Brundan–Ellis,
*Monoidal supercategories*, arXiv:1603.05928v3, §1.5.

## Implementation

The coherence isomorphisms of `Mat_ D` are *permutation matrices* `permMat e φ`: for a bijection
`e : ι ≃ κ` of index types and morphisms `φ i : X i ⟶ Y (e i)`, the matrix with entries `φ i` at
`(i, e i)` and zero elsewhere.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Limits Idempotents

universe v u

variable {D : Type u} [Category.{v} D] [Preadditive D]

namespace Mat_

open CategoryTheory.Mat_

/-! ## Permutation matrices -/

/-- The permutation matrix with entries `φ i` at `(i, e i)`. -/
def permMat {ι κ : Type} [Fintype ι] [Fintype κ] {X : ι → D} {Y : κ → D} (e : ι ≃ κ)
    (φ : ∀ i, X i ⟶ Y (e i)) : (⟨ι, X⟩ : Mat_ D) ⟶ ⟨κ, Y⟩ := by
  classical
  exact fun i j => if h : e i = j then φ i ≫ eqToHom (congrArg Y h) else 0

section Perm

variable {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ] {X : ι → D} {Y : κ → D}
  {Z : μ → D}

@[simp] theorem permMat_apply_self (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i)) (i : ι) :
    permMat e φ i (e i) = φ i := by
  simp [permMat]

theorem permMat_apply_of_ne (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i)) {i : ι} {j : κ} (h : e i ≠ j) :
    permMat e φ i j = 0 := by
  simp [permMat, h]

@[simp] theorem permMat_comp_apply (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i)) {N : Mat_ D}
    (g : (⟨κ, Y⟩ : Mat_ D) ⟶ N) (i : ι) (k : N.ι) :
    (permMat e φ ≫ g) i k = φ i ≫ g (e i) k := by
  classical
  rw [CategoryTheory.Mat_.comp_apply, Finset.sum_eq_single (e i)]
  · rw [permMat_apply_self]
  · intro j _ hj; rw [permMat_apply_of_ne e φ (Ne.symm hj), zero_comp]
  · intro h; exact absurd (Finset.mem_univ _) h

@[simp] theorem comp_permMat_apply (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i)) {M : Mat_ D}
    (f : M ⟶ (⟨ι, X⟩ : Mat_ D)) (m : M.ι) (i : ι) :
    (f ≫ permMat e φ) m (e i) = f m i ≫ φ i := by
  classical
  rw [CategoryTheory.Mat_.comp_apply, Finset.sum_eq_single i]
  · rw [permMat_apply_self]
  · intro j _ hj; rw [permMat_apply_of_ne e φ (fun h => hj (e.injective h)), comp_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype ι] in
/-- Morphisms into `⟨κ, Y⟩` are determined by their entries at `(m, e i)`. -/
theorem hom_ext_equiv (e : ι ≃ κ) {M : Mat_ D} {f g : M ⟶ (⟨κ, Y⟩ : Mat_ D)}
    (h : ∀ m i, f m (e i) = g m (e i)) : f = g := by
  ext m j
  have := h m (e.symm j)
  rwa [e.apply_symm_apply] at this

theorem permMat_congr {e e' : ι ≃ κ} (he : ∀ i, e i = e' i) (φ : ∀ i, X i ⟶ Y (e i))
    (φ' : ∀ i, X i ⟶ Y (e' i)) (hφ : ∀ i, φ i ≫ eqToHom (congrArg Y (he i)) = φ' i) :
    permMat e φ = permMat e' φ' := by
  ext i j
  by_cases h : e i = j
  · subst h
    rw [permMat_apply_self]
    unfold permMat
    rw [dif_pos (he i).symm, ← hφ i, Category.assoc, eqToHom_trans]
    simp
  · rw [permMat_apply_of_ne e φ h, permMat_apply_of_ne e' φ' (by rwa [← he i])]

theorem permMat_eq_id (e : ι ≃ ι) (he : ∀ i, e i = i) (φ : ∀ i, X i ⟶ X (e i))
    (hφ : ∀ i, φ i ≫ eqToHom (congrArg X (he i)) = 𝟙 (X i)) :
    permMat e φ = 𝟙 (⟨ι, X⟩ : Mat_ D) := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [CategoryTheory.Mat_.id_apply_self]
    unfold permMat
    rw [dif_pos (he i), hφ i]
  · rw [CategoryTheory.Mat_.id_apply_of_ne _ _ _ h, permMat_apply_of_ne e φ (by rwa [he i])]

theorem id_eq_permMat (ι : Type) [Fintype ι] (X : ι → D) :
    𝟙 (⟨ι, X⟩ : Mat_ D) = permMat (Equiv.refl ι) (fun i => 𝟙 (X i)) :=
  (permMat_eq_id (Equiv.refl ι) (fun _ => rfl) (fun i => 𝟙 (X i)) (fun _ => by simp)).symm

theorem permMat_comp_permMat (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i)) (e' : κ ≃ μ)
    (ψ : ∀ j, Y j ⟶ Z (e' j)) :
    permMat e φ ≫ permMat e' ψ = permMat (e.trans e') (fun i => φ i ≫ ψ (e i)) := by
  refine hom_ext_equiv (e.trans e') fun m i => ?_
  rw [permMat_comp_apply]
  by_cases h : m = i
  · subst h
    rw [Equiv.trans_apply, permMat_apply_self]
    exact (permMat_apply_self (e.trans e') (fun i => φ i ≫ ψ (e i)) m).symm
  · have h' : e m ≠ e i := fun h'' => h (e.injective h'')
    rw [Equiv.trans_apply, permMat_apply_of_ne e' ψ (fun h'' => h' (e'.injective h'')), comp_zero]
    exact (permMat_apply_of_ne (e.trans e') (fun i => φ i ≫ ψ (e i))
      (fun h'' => h ((e.trans e').injective h''))).symm

theorem id_eq_permMat' (M : Mat_ D) : 𝟙 M = permMat (Equiv.refl M.ι) (fun i => 𝟙 (M.X i)) :=
  id_eq_permMat M.ι M.X

end Perm

/-! ## The monoidal structure -/

section Monoidal

variable [MonoidalCategory D] [MonoidalPreadditive D]

/-- The tensor product `(Xᵢ)ᵢ ⊗ (Yⱼ)ⱼ = (Xᵢ ⊗ Yⱼ)_{(i, j)}`. -/
def tensorObj (M N : Mat_ D) : Mat_ D := ⟨M.ι × N.ι, fun x => M.X x.1 ⊗ N.X x.2⟩

/-- The entrywise tensor product of matrices. -/
def tensorHom {M M' N N' : Mat_ D} (f : M ⟶ M') (g : N ⟶ N') :
    tensorObj M N ⟶ tensorObj M' N' :=
  fun x y => f x.1 y.1 ⊗ g x.2 y.2

omit [MonoidalPreadditive D] in
@[simp] theorem tensorHom_apply {M M' N N' : Mat_ D} (f : M ⟶ M') (g : N ⟶ N')
    (x : M.ι × N.ι) (y : M'.ι × N'.ι) : tensorHom f g x y = f x.1 y.1 ⊗ g x.2 y.2 := rfl

/-- The unit object: `𝟙_ D` as a one-by-one matrix. -/
def unit : Mat_ D := ⟨PUnit, fun _ => 𝟙_ D⟩

theorem tensorHom_permMat {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    {X : ι → D} {Y : κ → D} {X' : ι' → D} {Y' : κ' → D} (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i))
    (e' : ι' ≃ κ') (ψ : ∀ i, X' i ⟶ Y' (e' i)) :
    tensorHom (permMat e φ) (permMat e' ψ) =
      permMat (X := fun x => X x.1 ⊗ X' x.2) (Y := fun y => Y y.1 ⊗ Y' y.2)
        (e.prodCongr e') (fun x => (φ x.1 ⊗ ψ x.2 : X x.1 ⊗ X' x.2 ⟶ Y (e x.1) ⊗ Y' (e' x.2))) := by
  ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  rw [tensorHom_apply]
  by_cases h₁ : e x₁ = y₁
  · by_cases h₂ : e' x₂ = y₂
    · subst h₁ h₂
      rw [permMat_apply_self, permMat_apply_self]
      exact (permMat_apply_self (X := fun x => X x.1 ⊗ X' x.2) (Y := fun y => Y y.1 ⊗ Y' y.2)
        (e.prodCongr e') (fun x => (φ x.1 ⊗ ψ x.2 : X x.1 ⊗ X' x.2 ⟶ Y (e x.1) ⊗ Y' (e' x.2)))
        (x₁, x₂)).symm
    · rw [permMat_apply_of_ne e' ψ h₂, MonoidalPreadditive.tensor_zero]
      exact (permMat_apply_of_ne (X := fun x => X x.1 ⊗ X' x.2) (Y := fun y => Y y.1 ⊗ Y' y.2)
        (e.prodCongr e') (fun x => (φ x.1 ⊗ ψ x.2 : X x.1 ⊗ X' x.2 ⟶ Y (e x.1) ⊗ Y' (e' x.2)))
        (i := (x₁, x₂)) (j := (y₁, y₂)) (fun h => h₂ (congrArg Prod.snd h))).symm
  · rw [permMat_apply_of_ne e φ h₁, MonoidalPreadditive.zero_tensor]
    exact (permMat_apply_of_ne (X := fun x => X x.1 ⊗ X' x.2) (Y := fun y => Y y.1 ⊗ Y' y.2)
      (e.prodCongr e') (fun x => (φ x.1 ⊗ ψ x.2 : X x.1 ⊗ X' x.2 ⟶ Y (e x.1) ⊗ Y' (e' x.2)))
      (i := (x₁, x₂)) (j := (y₁, y₂)) (fun h => h₁ (congrArg Prod.fst h))).symm

/-- The associator, a permutation matrix. -/
@[simps]
def associator (M N P : Mat_ D) : tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P) where
  hom := permMat (Equiv.prodAssoc M.ι N.ι P.ι) fun x => (α_ (M.X x.1.1) (N.X x.1.2) (P.X x.2)).hom
  inv := permMat (Equiv.prodAssoc M.ι N.ι P.ι).symm
    fun y => (α_ (M.X y.1) (N.X y.2.1) (P.X y.2.2)).inv
  hom_inv_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.hom_inv_id _
  inv_hom_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.inv_hom_id _

/-- The left unitor, a permutation matrix. -/
@[simps]
def leftUnitor (M : Mat_ D) : tensorObj unit M ≅ M where
  hom := permMat (Equiv.punitProd M.ι) fun x => (λ_ (M.X x.2)).hom
  inv := permMat (Equiv.punitProd M.ι).symm fun i => (λ_ (M.X i)).inv
  hom_inv_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.hom_inv_id _
  inv_hom_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.inv_hom_id _

/-- The right unitor, a permutation matrix. -/
@[simps]
def rightUnitor (M : Mat_ D) : tensorObj M unit ≅ M where
  hom := permMat (Equiv.prodPUnit M.ι) fun x => (ρ_ (M.X x.1)).hom
  inv := permMat (Equiv.prodPUnit M.ι).symm fun i => (ρ_ (M.X i)).inv
  hom_inv_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.hom_inv_id _
  inv_hom_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.inv_hom_id _

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Mat_ D) where
  tensorObj := tensorObj
  whiskerLeft M _ _ g := tensorHom (𝟙 M) g
  whiskerRight f N := tensorHom f (𝟙 N)
  tensorHom := tensorHom
  tensorUnit := unit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

theorem tensorHom_id_id (M N : Mat_ D) : tensorHom (𝟙 M) (𝟙 N) = 𝟙 (tensorObj M N) := by
  rw [id_eq_permMat' M, id_eq_permMat' N, tensorHom_permMat]
  exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by simp

theorem tensorHom_comp {M₁ M₂ M₃ N₁ N₂ N₃ : Mat_ D} (f₁ : M₁ ⟶ M₂) (f₂ : N₁ ⟶ N₂)
    (g₁ : M₂ ⟶ M₃) (g₂ : N₂ ⟶ N₃) :
    tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
  ext x z
  simp only [tensorHom_apply, CategoryTheory.Mat_.comp_apply, sum_tensor, tensor_sum]
  rw [Finset.sum_comm]
  refine Eq.trans ?_ (Fintype.sum_prod_type (f := fun y : M₂.ι × N₂.ι =>
    (f₁ x.1 y.1 ⊗ f₂ x.2 y.2) ≫ (g₁ y.1 z.1 ⊗ g₂ y.2 z.2))).symm
  simp only [tensor_comp]

/-- **The additive envelope of a monoidal preadditive category is monoidal.** -/
instance instMonoidalCategory : MonoidalCategory (Mat_ D) :=
  MonoidalCategory.ofTensorHom
    (tensor_id := tensorHom_id_id)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensor_comp := tensorHom_comp)
    (associator_naturality := fun {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ => by
      refine hom_ext_equiv (Equiv.prodAssoc Y₁.ι Y₂.ι Y₃.ι) fun m i => ?_
      change (tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom) m _ =
        ((associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃)) m _
      rw [associator_hom, associator_hom]
      refine (comp_permMat_apply
        (X := fun x : (Y₁.ι × Y₂.ι) × Y₃.ι => (Y₁.X x.1.1 ⊗ Y₂.X x.1.2) ⊗ Y₃.X x.2)
        (Y := fun y : Y₁.ι × (Y₂.ι × Y₃.ι) => Y₁.X y.1 ⊗ (Y₂.X y.2.1 ⊗ Y₃.X y.2.2))
        (Equiv.prodAssoc Y₁.ι Y₂.ι Y₃.ι)
        (fun x => (α_ (Y₁.X x.1.1) (Y₂.X x.1.2) (Y₃.X x.2)).hom)
        (tensorHom (tensorHom f₁ f₂) f₃) m i).trans ?_
      refine Eq.trans ?_ (permMat_comp_apply
        (X := fun x : (X₁.ι × X₂.ι) × X₃.ι => (X₁.X x.1.1 ⊗ X₂.X x.1.2) ⊗ X₃.X x.2)
        (Y := fun y : X₁.ι × (X₂.ι × X₃.ι) => X₁.X y.1 ⊗ (X₂.X y.2.1 ⊗ X₃.X y.2.2))
        (Equiv.prodAssoc X₁.ι X₂.ι X₃.ι)
        (fun x => (α_ (X₁.X x.1.1) (X₂.X x.1.2) (X₃.X x.2)).hom)
        (tensorHom f₁ (tensorHom f₂ f₃)) m _).symm
      exact MonoidalCategory.associator_naturality _ _ _)
    (leftUnitor_naturality := fun {X Y} f => by
      refine hom_ext_equiv (Equiv.punitProd Y.ι) fun m i => ?_
      change (tensorHom (𝟙 unit) f ≫ (leftUnitor Y).hom) m _ = ((leftUnitor X).hom ≫ f) m _
      rw [leftUnitor_hom, leftUnitor_hom]
      refine (comp_permMat_apply (Equiv.punitProd Y.ι) (fun x => (λ_ (Y.X x.2)).hom)
        (tensorHom (𝟙 unit) f) m i).trans ?_
      refine Eq.trans ?_ (permMat_comp_apply (Equiv.punitProd X.ι) (fun x => (λ_ (X.X x.2)).hom)
        f m _).symm
      obtain ⟨⟨⟩, m⟩ := m
      obtain ⟨⟨⟩, i⟩ := i
      rw [tensorHom_apply, CategoryTheory.Mat_.id_apply_self, id_tensorHom]
      exact MonoidalCategory.leftUnitor_naturality _)
    (rightUnitor_naturality := fun {X Y} f => by
      refine hom_ext_equiv (Equiv.prodPUnit Y.ι) fun m i => ?_
      change (tensorHom f (𝟙 unit) ≫ (rightUnitor Y).hom) m _ = ((rightUnitor X).hom ≫ f) m _
      rw [rightUnitor_hom, rightUnitor_hom]
      refine (comp_permMat_apply (Equiv.prodPUnit Y.ι) (fun x => (ρ_ (Y.X x.1)).hom)
        (tensorHom f (𝟙 unit)) m i).trans ?_
      refine Eq.trans ?_ (permMat_comp_apply (Equiv.prodPUnit X.ι) (fun x => (ρ_ (X.X x.1)).hom)
        f m _).symm
      obtain ⟨m, ⟨⟩⟩ := m
      obtain ⟨i, ⟨⟩⟩ := i
      rw [tensorHom_apply, CategoryTheory.Mat_.id_apply_self, tensorHom_id]
      exact MonoidalCategory.rightUnitor_naturality _)
    (pentagon := fun W X Y Z => by
      change tensorHom (associator W X Y).hom (𝟙 Z) ≫ (associator W (tensorObj X Y) Z).hom ≫
          tensorHom (𝟙 W) (associator X Y Z).hom =
        (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom
      rw [associator_hom, associator_hom, associator_hom, associator_hom, associator_hom,
        id_eq_permMat' Z, id_eq_permMat' W, tensorHom_permMat, tensorHom_permMat,
        permMat_comp_permMat, permMat_comp_permMat, permMat_comp_permMat]
      refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
      rw [eqToHom_refl, Category.comp_id]
      simp only [id_tensorHom, tensorHom_id]
      exact MonoidalCategory.pentagon _ _ _ _)
    (triangle := fun X Y => by
      change (associator X unit Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
        tensorHom (rightUnitor X).hom (𝟙 Y)
      rw [associator_hom, leftUnitor_hom, rightUnitor_hom, id_eq_permMat' X, id_eq_permMat' Y,
        tensorHom_permMat, tensorHom_permMat, permMat_comp_permMat]
      refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
      rw [eqToHom_refl, Category.comp_id]
      simp only [id_tensorHom, tensorHom_id]
      exact MonoidalCategory.triangle _ _)

omit [MonoidalPreadditive D] in
theorem tensorObj_def (M N : Mat_ D) : M ⊗ N = tensorObj M N := rfl

omit [MonoidalPreadditive D] in
theorem tensorHom_def' {M M' N N' : Mat_ D} (f : M ⟶ M') (g : N ⟶ N') : f ⊗ g = tensorHom f g :=
  rfl

omit [MonoidalPreadditive D] in
theorem tensorUnit_def : 𝟙_ (Mat_ D) = unit := rfl

instance instMonoidalPreadditive : MonoidalPreadditive (Mat_ D) where
  whiskerLeft_zero := by
    intros; ext; exact MonoidalPreadditive.tensor_zero _
  zero_whiskerRight := by
    intros; ext; exact MonoidalPreadditive.zero_tensor _
  whiskerLeft_add := by
    intros; ext; simp [MonoidalCategoryStruct.whiskerLeft, MonoidalPreadditive.tensor_add]
  add_whiskerRight := by
    intros; ext; simp [MonoidalCategoryStruct.whiskerRight, MonoidalPreadditive.add_tensor]

end Monoidal

end Mat_

/-! ## The idempotent completion -/

namespace Karoubi

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The tensor product `(X, p) ⊗ (Y, q) = (X ⊗ Y, p ⊗ q)`. -/
@[simps]
def tensorObj (P Q : Karoubi C) : Karoubi C :=
  ⟨P.X ⊗ Q.X, P.p ⊗ Q.p, by rw [← tensor_comp, P.idem, Q.idem]⟩

/-- The tensor product of morphisms. -/
@[simps]
def tensorHom {P P' Q Q' : Karoubi C} (f : P ⟶ P') (g : Q ⟶ Q') :
    tensorObj P Q ⟶ tensorObj P' Q' :=
  ⟨f.f ⊗ g.f, by
    show _ = (P.p ⊗ Q.p) ≫ (f.f ⊗ g.f) ≫ (P'.p ⊗ Q'.p)
    rw [← tensor_comp, ← tensor_comp, ← f.comm, ← g.comm]⟩

/-- The unit object `(𝟙_, 𝟙)`. -/
@[simps]
def unit : Karoubi C := ⟨𝟙_ C, 𝟙 _, by simp⟩

@[reassoc]
theorem tensor_p_idem (P Q : Karoubi C) : (P.p ⊗ Q.p) ≫ (P.p ⊗ Q.p) = P.p ⊗ Q.p := by
  rw [← tensor_comp, P.idem, Q.idem]

/-- The associator `(α ≫ (p ⊗ (q ⊗ r)))`. -/
@[simps]
def associator (P Q R : Karoubi C) : tensorObj (tensorObj P Q) R ≅ tensorObj P (tensorObj Q R) where
  hom := ⟨(α_ P.X Q.X R.X).hom ≫ (P.p ⊗ (Q.p ⊗ R.p)), by
    show _ = ((P.p ⊗ Q.p) ⊗ R.p) ≫ ((α_ P.X Q.X R.X).hom ≫ (P.p ⊗ (Q.p ⊗ R.p))) ≫
      (P.p ⊗ (Q.p ⊗ R.p))
    rw [Category.assoc, associator_naturality_assoc]
    simp only [← tensor_comp, P.idem, Q.idem, R.idem]⟩
  inv := ⟨(α_ P.X Q.X R.X).inv ≫ ((P.p ⊗ Q.p) ⊗ R.p), by
    show _ = (P.p ⊗ (Q.p ⊗ R.p)) ≫ ((α_ P.X Q.X R.X).inv ≫ ((P.p ⊗ Q.p) ⊗ R.p)) ≫
      ((P.p ⊗ Q.p) ⊗ R.p)
    rw [Category.assoc, associator_inv_naturality_assoc]
    simp only [← tensor_comp, P.idem, Q.idem, R.idem]⟩
  hom_inv_id := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [Idempotents.Karoubi.comp_f, Idempotents.Karoubi.id_f, tensorObj_p, Category.assoc]
    rw [associator_inv_naturality_assoc, Iso.hom_inv_id_assoc]
    simp only [← tensor_comp, P.idem, Q.idem, R.idem])
  inv_hom_id := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [Idempotents.Karoubi.comp_f, Idempotents.Karoubi.id_f, tensorObj_p, Category.assoc]
    rw [associator_naturality_assoc, Iso.inv_hom_id_assoc]
    simp only [← tensor_comp, P.idem, Q.idem, R.idem])

/-- The left unitor `λ ≫ p`. -/
@[simps]
def leftUnitor (P : Karoubi C) : tensorObj unit P ≅ P where
  hom := ⟨(λ_ P.X).hom ≫ P.p, by
    show _ = (𝟙 (𝟙_ C) ⊗ P.p) ≫ ((λ_ P.X).hom ≫ P.p) ≫ P.p
    rw [id_tensorHom, Category.assoc, leftUnitor_naturality_assoc, P.idem, P.idem]⟩
  inv := ⟨P.p ≫ (λ_ P.X).inv, by
    show _ = P.p ≫ (P.p ≫ (λ_ P.X).inv) ≫ (𝟙 (𝟙_ C) ⊗ P.p)
    rw [id_tensorHom, Category.assoc, ← leftUnitor_inv_naturality, P.idem_assoc, P.idem_assoc]⟩
  hom_inv_id := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [Idempotents.Karoubi.comp_f, Idempotents.Karoubi.id_f, tensorObj_p, unit_p,
      Category.assoc, P.idem_assoc]
    rw [leftUnitor_inv_naturality, Iso.hom_inv_id_assoc]
    exact (id_tensorHom _ _).symm)
  inv_hom_id := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [Idempotents.Karoubi.comp_f, Idempotents.Karoubi.id_f, Category.assoc,
      Iso.inv_hom_id_assoc, P.idem])

/-- The right unitor `ρ ≫ p`. -/
@[simps]
def rightUnitor (P : Karoubi C) : tensorObj P unit ≅ P where
  hom := ⟨(ρ_ P.X).hom ≫ P.p, by
    show _ = (P.p ⊗ 𝟙 (𝟙_ C)) ≫ ((ρ_ P.X).hom ≫ P.p) ≫ P.p
    rw [tensorHom_id, Category.assoc, rightUnitor_naturality_assoc, P.idem, P.idem]⟩
  inv := ⟨P.p ≫ (ρ_ P.X).inv, by
    show _ = P.p ≫ (P.p ≫ (ρ_ P.X).inv) ≫ (P.p ⊗ 𝟙 (𝟙_ C))
    rw [tensorHom_id, Category.assoc, ← rightUnitor_inv_naturality, P.idem_assoc, P.idem_assoc]⟩
  hom_inv_id := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [Idempotents.Karoubi.comp_f, Idempotents.Karoubi.id_f, tensorObj_p, unit_p,
      Category.assoc, P.idem_assoc]
    rw [rightUnitor_inv_naturality, Iso.hom_inv_id_assoc]
    exact (tensorHom_id _ _).symm)
  inv_hom_id := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [Idempotents.Karoubi.comp_f, Idempotents.Karoubi.id_f, Category.assoc,
      Iso.inv_hom_id_assoc, P.idem])

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Karoubi C) where
  tensorObj := tensorObj
  whiskerLeft P _ _ g := tensorHom (𝟙 P) g
  whiskerRight f Q := tensorHom f (𝟙 Q)
  tensorHom := tensorHom
  tensorUnit := unit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

omit [MonoidalCategory C] in
/-- `(φ ≫ E) ≫ (ψ ≫ E') = (φ ≫ ψ) ≫ E'` when `E ≫ ψ = ψ ≫ E'` and `E'` is idempotent. -/
theorem sandwich {X Y Z W : C} (φ : X ⟶ Y) (E : Y ⟶ Y) (ψ : Y ⟶ Z) (E' : Z ⟶ Z)
    (h : E ≫ ψ = ψ ≫ E') (hE' : E' ≫ E' = E') (W' : Z ⟶ W) :
    (φ ≫ E) ≫ (ψ ≫ E') ≫ W' = (φ ≫ ψ) ≫ E' ≫ W' := by
  simp only [Category.assoc]
  rw [reassoc_of% h, reassoc_of% hE']

omit [MonoidalCategory C] in
theorem sandwich' {X Y Z : C} (φ : X ⟶ Y) (E : Y ⟶ Y) (ψ : Y ⟶ Z) (E' : Z ⟶ Z)
    (h : E ≫ ψ = ψ ≫ E') (hE' : E' ≫ E' = E') :
    (φ ≫ E) ≫ (ψ ≫ E') = (φ ≫ ψ) ≫ E' := by
  simpa using sandwich φ E ψ E' h hE' (𝟙 _)

/-- **The idempotent completion of a monoidal category is monoidal.** -/
instance instMonoidalCategory : MonoidalCategory (Karoubi C) :=
  MonoidalCategory.ofTensorHom
    (tensor_id := fun _ _ => rfl)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensor_comp := fun _ _ _ _ => Idempotents.Karoubi.hom_ext _ _ (tensor_comp _ _ _ _))
    (associator_naturality := fun {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ =>
      Idempotents.Karoubi.hom_ext _ _ (by
      change ((f₁.f ⊗ f₂.f) ⊗ f₃.f) ≫ (α_ Y₁.X Y₂.X Y₃.X).hom ≫ (Y₁.p ⊗ (Y₂.p ⊗ Y₃.p)) =
        ((α_ X₁.X X₂.X X₃.X).hom ≫ (X₁.p ⊗ (X₂.p ⊗ X₃.p))) ≫ (f₁.f ⊗ (f₂.f ⊗ f₃.f))
      rw [associator_naturality_assoc, Category.assoc]
      simp only [← tensor_comp, Idempotents.Karoubi.comp_p, Idempotents.Karoubi.p_comp]))
    (leftUnitor_naturality := fun {X Y} f => Idempotents.Karoubi.hom_ext _ _ (by
      change (𝟙 (𝟙_ C) ⊗ f.f) ≫ (λ_ Y.X).hom ≫ Y.p = ((λ_ X.X).hom ≫ X.p) ≫ f.f
      rw [id_tensorHom, leftUnitor_naturality_assoc, Category.assoc,
        Idempotents.Karoubi.comp_p, Idempotents.Karoubi.p_comp]))
    (rightUnitor_naturality := fun {X Y} f => Idempotents.Karoubi.hom_ext _ _ (by
      change (f.f ⊗ 𝟙 (𝟙_ C)) ≫ (ρ_ Y.X).hom ≫ Y.p = ((ρ_ X.X).hom ≫ X.p) ≫ f.f
      rw [tensorHom_id, rightUnitor_naturality_assoc, Category.assoc,
        Idempotents.Karoubi.comp_p, Idempotents.Karoubi.p_comp]))
    (pentagon := fun W X Y Z => Idempotents.Karoubi.hom_ext _ _ (by
      change (((α_ W.X X.X Y.X).hom ≫ (W.p ⊗ (X.p ⊗ Y.p))) ⊗ Z.p) ≫
          ((α_ W.X (X.X ⊗ Y.X) Z.X).hom ≫ (W.p ⊗ ((X.p ⊗ Y.p) ⊗ Z.p))) ≫
            (W.p ⊗ ((α_ X.X Y.X Z.X).hom ≫ (X.p ⊗ (Y.p ⊗ Z.p)))) =
        ((α_ (W.X ⊗ X.X) Y.X Z.X).hom ≫ ((W.p ⊗ X.p) ⊗ (Y.p ⊗ Z.p))) ≫
          ((α_ W.X X.X (Y.X ⊗ Z.X)).hom ≫ (W.p ⊗ (X.p ⊗ (Y.p ⊗ Z.p))))
      have e1 : ((α_ W.X X.X Y.X).hom ≫ (W.p ⊗ (X.p ⊗ Y.p))) ⊗ Z.p =
          ((α_ W.X X.X Y.X).hom ⊗ 𝟙 Z.X) ≫ ((W.p ⊗ (X.p ⊗ Y.p)) ⊗ Z.p) := by
        rw [← tensor_comp, Category.id_comp]
      have e3 : W.p ⊗ ((α_ X.X Y.X Z.X).hom ≫ (X.p ⊗ (Y.p ⊗ Z.p))) =
          (𝟙 W.X ⊗ (α_ X.X Y.X Z.X).hom) ≫ (W.p ⊗ (X.p ⊗ (Y.p ⊗ Z.p))) := by
        rw [← tensor_comp, Category.id_comp]
      have i4 : ∀ {A B C' D' : C} (a : A ⟶ A) (b : B ⟶ B) (c : C' ⟶ C') (d : D' ⟶ D'),
          a ≫ a = a → b ≫ b = b → c ≫ c = c → d ≫ d = d →
          (a ⊗ (b ⊗ (c ⊗ d))) ≫ (a ⊗ (b ⊗ (c ⊗ d))) = a ⊗ (b ⊗ (c ⊗ d)) := by
        intros A B C' D' a b c d ha hb hc hd
        simp only [← tensor_comp, ha, hb, hc, hd]
      have idem := i4 W.p X.p Y.p Z.p W.idem X.idem Y.idem Z.idem
      have c1 : ((W.p ⊗ (X.p ⊗ Y.p)) ⊗ Z.p) ≫ (α_ W.X (X.X ⊗ Y.X) Z.X).hom =
          (α_ W.X (X.X ⊗ Y.X) Z.X).hom ≫ (W.p ⊗ ((X.p ⊗ Y.p) ⊗ Z.p)) :=
        associator_naturality _ _ _
      have c2 : (W.p ⊗ ((X.p ⊗ Y.p) ⊗ Z.p)) ≫ (𝟙 W.X ⊗ (α_ X.X Y.X Z.X).hom) =
          (𝟙 W.X ⊗ (α_ X.X Y.X Z.X).hom) ≫ (W.p ⊗ (X.p ⊗ (Y.p ⊗ Z.p))) := by
        rw [← tensor_comp, ← tensor_comp, Category.id_comp, Category.comp_id,
          associator_naturality]
      have c12 : ((W.p ⊗ (X.p ⊗ Y.p)) ⊗ Z.p) ≫ ((α_ W.X (X.X ⊗ Y.X) Z.X).hom ≫
          (𝟙 W.X ⊗ (α_ X.X Y.X Z.X).hom)) = ((α_ W.X (X.X ⊗ Y.X) Z.X).hom ≫
          (𝟙 W.X ⊗ (α_ X.X Y.X Z.X).hom)) ≫ (W.p ⊗ (X.p ⊗ (Y.p ⊗ Z.p))) := by
        rw [reassoc_of% c1, c2, Category.assoc]
      have c3 : ((W.p ⊗ X.p) ⊗ (Y.p ⊗ Z.p)) ≫ (α_ W.X X.X (Y.X ⊗ Z.X)).hom =
          (α_ W.X X.X (Y.X ⊗ Z.X)).hom ≫ (W.p ⊗ (X.p ⊗ (Y.p ⊗ Z.p))) :=
        associator_naturality _ _ _
      rw [e1, e3, sandwich' _ _ _ _ c2 idem, sandwich' _ _ _ _ c12 idem,
        sandwich' _ _ _ _ c3 idem]
      congr 1
      simp only [Category.assoc, tensorHom_id, id_tensorHom]
      exact MonoidalCategory.pentagon _ _ _ _))
    (triangle := fun X Y => Idempotents.Karoubi.hom_ext _ _ (by
      change ((α_ X.X (𝟙_ C) Y.X).hom ≫ (X.p ⊗ (𝟙 (𝟙_ C) ⊗ Y.p))) ≫
          (X.p ⊗ ((λ_ Y.X).hom ≫ Y.p)) = ((ρ_ X.X).hom ≫ X.p) ⊗ Y.p
      have e1 : X.p ⊗ ((λ_ Y.X).hom ≫ Y.p) = (𝟙 X.X ⊗ (λ_ Y.X).hom) ≫ (X.p ⊗ Y.p) := by
        rw [← tensor_comp, Category.id_comp]
      have e2 : ((ρ_ X.X).hom ≫ X.p) ⊗ Y.p = ((ρ_ X.X).hom ⊗ 𝟙 Y.X) ≫ (X.p ⊗ Y.p) := by
        rw [← tensor_comp, Category.id_comp]
      have c : (X.p ⊗ (𝟙 (𝟙_ C) ⊗ Y.p)) ≫ (𝟙 X.X ⊗ (λ_ Y.X).hom) =
          (𝟙 X.X ⊗ (λ_ Y.X).hom) ≫ (X.p ⊗ Y.p) := by
        rw [← tensor_comp, ← tensor_comp, Category.id_comp, Category.comp_id, id_tensorHom,
          leftUnitor_naturality]
      have idem : (X.p ⊗ Y.p) ≫ (X.p ⊗ Y.p) = X.p ⊗ Y.p := by
        rw [← tensor_comp, X.idem, Y.idem]
      rw [e1, e2, sandwich' _ _ _ _ c idem]
      congr 1
      simp only [tensorHom_id, id_tensorHom]
      exact MonoidalCategory.triangle _ _))

theorem tensorObj_def (P Q : Karoubi C) : P ⊗ Q = tensorObj P Q := rfl

@[simp] theorem tensorObj_X' (P Q : Karoubi C) : (P ⊗ Q).X = P.X ⊗ Q.X := rfl

@[simp] theorem tensorObj_p' (P Q : Karoubi C) : (P ⊗ Q).p = P.p ⊗ Q.p := rfl

@[simp] theorem tensorHom_f' {P P' Q Q' : Karoubi C} (f : P ⟶ P') (g : Q ⟶ Q') :
    (f ⊗ g).f = f.f ⊗ g.f := rfl

@[simp] theorem whiskerLeft_f (P : Karoubi C) {Q Q' : Karoubi C} (g : Q ⟶ Q') :
    (P ◁ g).f = P.p ⊗ g.f := rfl

@[simp] theorem whiskerRight_f {P P' : Karoubi C} (f : P ⟶ P') (Q : Karoubi C) :
    (f ▷ Q).f = f.f ⊗ Q.p := rfl

@[simp] theorem tensorUnit_X : (𝟙_ (Karoubi C)).X = 𝟙_ C := rfl

@[simp] theorem tensorUnit_p : (𝟙_ (Karoubi C)).p = 𝟙 (𝟙_ C) := rfl

instance instMonoidalPreadditive [Preadditive C] [MonoidalPreadditive C] :
    MonoidalPreadditive (Karoubi C) where
  whiskerLeft_zero := Idempotents.Karoubi.hom_ext _ _ (MonoidalPreadditive.tensor_zero _)
  zero_whiskerRight := Idempotents.Karoubi.hom_ext _ _ (MonoidalPreadditive.zero_tensor _)
  whiskerLeft_add _ _ := Idempotents.Karoubi.hom_ext _ _ (MonoidalPreadditive.tensor_add _ _ _)
  add_whiskerRight _ _ := Idempotents.Karoubi.hom_ext _ _ (MonoidalPreadditive.add_tensor _ _ _)

end Karoubi

end StringDiagrams
