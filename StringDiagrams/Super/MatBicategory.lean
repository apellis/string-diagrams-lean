import StringDiagrams.Super.BicategoryOfHcomp
import StringDiagrams.Super.SKarMonoidalPi
import StringDiagrams.Super.QPiTwoCategory

/-!
# The additive envelope of a bicategory

For a bicategory `B` whose hom categories are preadditive with additive whiskerings
(`PreadditiveBicategory B`), the *additive envelope* `MatBicat B` has the same objects, the
hom categories `Mat_ (a ⟶ b)` (Mathlib's additive envelope: formal finite direct sums
`(fᵢ)ᵢ` of 1-morphisms and matrices of 2-morphisms), horizontal composition
`(fᵢ)ᵢ ≫ (gⱼ)ⱼ = (fᵢ ≫ gⱼ)_{(i, j)}` extended bilinearly to matrices (`MatBicat.hcomp`),
and coherence isomorphisms given by permutation matrices (`StringDiagrams.Mat_.permMat`).
It is a bicategory (`MatBicat.instBicategory`), preadditive and `R`-linear when `B` is.

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (the
end of the section), a Π-2-category structure (Definition 5.2) and a `(Q, Π)`-2-category
structure (Definition 6.14) on `B` extend to `MatBicat B` (`MatBicat.instPiTwoCategory`,
`MatBicat.instQPiTwoCategory`), with `π_λ`, `q_λ`, `q_λ⁻¹` the one-by-one matrices and `β`,
`γ`, `ξ`, `ii`, `jj` extended entrywise. This is the first half of the additive Karoubi envelope
of a 2-category (`StringDiagrams.Super.KaroubiBicategory` is the second half).

Compositions of 1-morphisms are written in diagrammatic order.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u w₁

/-- The additive envelope of a bicategory: the same objects, with hom categories the additive
envelopes `Mat_ (a ⟶ b)`. -/
@[ext]
structure MatBicat (B : Type u) where
  /-- The object of `B`. -/
  obj : B

namespace MatBicat

open StringDiagrams.Mat_ CategoryTheory.Mat_ PreadditiveBicategory

section Basic

variable {B : Type u} [Bicategory.{w, v} B]

instance instCategoryStruct : CategoryStruct (MatBicat B) where
  Hom a b := Mat_ (a.obj ⟶ b.obj)
  id a := ⟨PUnit, fun _ => 𝟙 a.obj⟩
  comp M N := ⟨M.ι × N.ι, fun x => M.X x.1 ≫ N.X x.2⟩

/-- A 1-morphism of `B` as a one-by-one matrix. -/
abbrev single {a b : B} (f : a ⟶ b) : (⟨a⟩ : MatBicat B) ⟶ ⟨b⟩ := ⟨PUnit, fun _ => f⟩

@[simp] theorem single_ι {a b : B} (f : a ⟶ b) : (single f).ι = PUnit := rfl

@[simp] theorem single_X {a b : B} (f : a ⟶ b) (x) : (single f).X x = f := rfl

theorem id_eq (a : MatBicat B) : 𝟙 a = single (𝟙 a.obj) := rfl

@[simp] theorem comp_ι {a b c : MatBicat B} (M : a ⟶ b) (N : b ⟶ c) :
    (M ≫ N).ι = (M.ι × N.ι) := rfl

@[simp] theorem comp_X {a b c : MatBicat B} (M : a ⟶ b) (N : b ⟶ c) (x : M.ι × N.ι) :
    (M ≫ N).X x = M.X x.1 ≫ N.X x.2 := rfl

end Basic

section Preadditive

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]

instance (a b : MatBicat B) : Category (a ⟶ b) :=
  inferInstanceAs (Category (Mat_ (a.obj ⟶ b.obj)))

instance (a b : MatBicat B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (Mat_ (a.obj ⟶ b.obj)))

instance (a b : MatBicat B) : Limits.HasFiniteBiproducts (a ⟶ b) :=
  inferInstanceAs (Limits.HasFiniteBiproducts (Mat_ (a.obj ⟶ b.obj)))

variable {a b c d : MatBicat B}

/-- Horizontal composition of matrices, extended bilinearly: the entry at
`((i, j), (i', j'))` is the horizontal composite `f i i' ▷ _ ≫ _ ◁ g j j'`. -/
def hcomp {M M' : a ⟶ b} {N N' : b ⟶ c} (f : M ⟶ M') (g : N ⟶ N') : M ≫ N ⟶ M' ≫ N' :=
  fun x y => hcomp₂ (f x.1 y.1) (g x.2 y.2)

@[simp] theorem hcomp_apply {M M' : a ⟶ b} {N N' : b ⟶ c} (f : M ⟶ M') (g : N ⟶ N')
    (x : M.ι × N.ι) (y : M'.ι × N'.ι) : hcomp f g x y = hcomp₂ (f x.1 y.1) (g x.2 y.2) := rfl

/-! Entrywise lemmas for 2-morphisms, restated for the hom categories of `MatBicat B`. -/

theorem comp_apply {M N K : a ⟶ b} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j, f i j ≫ g j k :=
  CategoryTheory.Mat_.comp_apply f g i k

theorem id_apply_self (M : a ⟶ b) (i : M.ι) : (𝟙 M : M ⟶ M) i i = 𝟙 _ :=
  CategoryTheory.Mat_.id_apply_self M i

theorem id_apply_of_ne (M : a ⟶ b) (i j : M.ι) (h : i ≠ j) : (𝟙 M : M ⟶ M) i j = 0 :=
  CategoryTheory.Mat_.id_apply_of_ne M i j h

@[simp] theorem add_apply {M N : a ⟶ b} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j := rfl

@[simp] theorem neg_apply {M N : a ⟶ b} (f : M ⟶ N) (i j) : (-f) i j = -f i j := rfl

@[simp] theorem zero_apply {M N : a ⟶ b} (i j) : (0 : M ⟶ N) i j = 0 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The associator, a permutation matrix. -/
@[simps]
def associator (M : a ⟶ b) (N : b ⟶ c) (P : c ⟶ d) : (M ≫ N) ≫ P ≅ M ≫ N ≫ P where
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

set_option backward.isDefEq.respectTransparency false in
/-- The left unitor, a permutation matrix. -/
@[simps]
def leftUnitor (M : a ⟶ b) : 𝟙 a ≫ M ≅ M where
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

set_option backward.isDefEq.respectTransparency false in
/-- The right unitor, a permutation matrix. -/
@[simps]
def rightUnitor (M : a ⟶ b) : M ≫ 𝟙 b ≅ M where
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

end Preadditive

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B]

/-! ## Horizontal composition of matrices -/

section Hcomp

variable {a b c : MatBicat B}

theorem hcomp₂_zero_left {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (θ : h ⟶ i) :
    hcomp₂ (0 : f ⟶ g) θ = 0 := by
  simp [hcomp₂]

theorem hcomp₂_zero_right {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) :
    hcomp₂ η (0 : h ⟶ i) = 0 := by
  simp [hcomp₂]

theorem hcomp_permMat {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    {X : ι → (a.obj ⟶ b.obj)} {Y : κ → (a.obj ⟶ b.obj)} {X' : ι' → (b.obj ⟶ c.obj)}
    {Y' : κ' → (b.obj ⟶ c.obj)} (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i))
    (e' : ι' ≃ κ') (ψ : ∀ i, X' i ⟶ Y' (e' i)) :
    hcomp (M := ⟨ι, X⟩) (M' := ⟨κ, Y⟩) (N := ⟨ι', X'⟩) (N' := ⟨κ', Y'⟩)
        (permMat e φ) (permMat e' ψ) =
      permMat (X := fun x => X x.1 ≫ X' x.2) (Y := fun y => Y y.1 ≫ Y' y.2)
        (e.prodCongr e') (fun x => hcomp₂ (φ x.1) (ψ x.2)) := by
  apply CategoryTheory.Mat_.hom_ext
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  rw [hcomp_apply]
  by_cases h₁ : e x₁ = y₁
  · by_cases h₂ : e' x₂ = y₂
    · subst h₁ h₂
      rw [permMat_apply_self, permMat_apply_self]
      exact (permMat_apply_self (X := fun x => X x.1 ≫ X' x.2) (Y := fun y => Y y.1 ≫ Y' y.2)
        (e.prodCongr e') (fun x => hcomp₂ (φ x.1) (ψ x.2)) (x₁, x₂)).symm
    · rw [permMat_apply_of_ne e' ψ h₂, hcomp₂_zero_right]
      exact (permMat_apply_of_ne (X := fun x => X x.1 ≫ X' x.2) (Y := fun y => Y y.1 ≫ Y' y.2)
        (e.prodCongr e') (fun x => hcomp₂ (φ x.1) (ψ x.2))
        (i := (x₁, x₂)) (j := (y₁, y₂)) (fun h => h₂ (congrArg Prod.snd h))).symm
  · rw [permMat_apply_of_ne e φ h₁, hcomp₂_zero_left]
    exact (permMat_apply_of_ne (X := fun x => X x.1 ≫ X' x.2) (Y := fun y => Y y.1 ≫ Y' y.2)
      (e.prodCongr e') (fun x => hcomp₂ (φ x.1) (ψ x.2))
      (i := (x₁, x₂)) (j := (y₁, y₂)) (fun h => h₁ (congrArg Prod.fst h))).symm

set_option backward.isDefEq.respectTransparency false in
theorem hcomp_id_id (M : a ⟶ b) (N : b ⟶ c) : hcomp (𝟙 M) (𝟙 N) = 𝟙 (M ≫ N) := by
  rw [id_eq_permMat' M, id_eq_permMat' N, hcomp_permMat]
  exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by simp [hcomp₂]

theorem sum_whiskerRight {a b c : B} {f g : a ⟶ b} {α : Type*} (s : Finset α)
    (η : α → (f ⟶ g)) (h : b ⟶ c) : (∑ i ∈ s, η i) ▷ h = ∑ i ∈ s, η i ▷ h :=
  (postcomp a h).map_sum η s

theorem whiskerLeft_sum {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} {α : Type*} (s : Finset α)
    (θ : α → (g ⟶ h)) : f ◁ (∑ i ∈ s, θ i) = ∑ i ∈ s, f ◁ θ i :=
  (precomp c f).map_sum θ s

theorem hcomp_comp {M₁ M₂ M₃ : a ⟶ b} {N₁ N₂ N₃ : b ⟶ c} (f₁ : M₁ ⟶ M₂) (f₂ : N₁ ⟶ N₂)
    (g₁ : M₂ ⟶ M₃) (g₂ : N₂ ⟶ N₃) :
    hcomp (f₁ ≫ g₁) (f₂ ≫ g₂) = hcomp f₁ f₂ ≫ hcomp g₁ g₂ := by
  apply CategoryTheory.Mat_.hom_ext
  intro x z
  simp only [hcomp_apply, comp_apply, hcomp₂, sum_whiskerRight,
    whiskerLeft_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Eq.trans ?_ (Fintype.sum_prod_type (f := fun y : M₂.ι × N₂.ι =>
    (f₁ x.1 y.1 ▷ N₁.X x.2 ≫ M₂.X y.1 ◁ f₂ x.2 y.2) ≫
      (g₁ y.1 z.1 ▷ N₂.X y.2 ≫ M₃.X z.1 ◁ g₂ y.2 z.2))).symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  exact hcomp₂_comp (f₁ x.1 j) (g₁ j z.1) (f₂ x.2 k) (g₂ k z.2)

end Hcomp

/-! ## The bicategory -/

set_option backward.isDefEq.respectTransparency false in
/-- **The additive envelope of a bicategory is a bicategory.** -/
instance instBicategory : Bicategory (MatBicat B) :=
  Bicategory.ofHcomp hcomp associator leftUnitor rightUnitor hcomp_id_id
    (fun η η' θ θ' => hcomp_comp η θ η' θ')
    (fun {a b c d X₁ Y₁ X₂ Y₂ X₃ Y₃} f₁ f₂ f₃ => by
      refine hom_ext_equiv (Equiv.prodAssoc Y₁.ι Y₂.ι Y₃.ι) fun m i => ?_
      rw [associator_hom, associator_hom]
      refine (comp_permMat_apply
        (X := fun x : (Y₁.ι × Y₂.ι) × Y₃.ι => (Y₁.X x.1.1 ≫ Y₂.X x.1.2) ≫ Y₃.X x.2)
        (Y := fun y : Y₁.ι × (Y₂.ι × Y₃.ι) => Y₁.X y.1 ≫ (Y₂.X y.2.1 ≫ Y₃.X y.2.2))
        (Equiv.prodAssoc Y₁.ι Y₂.ι Y₃.ι)
        (fun x => (α_ (Y₁.X x.1.1) (Y₂.X x.1.2) (Y₃.X x.2)).hom)
        (hcomp (hcomp f₁ f₂) f₃) m i).trans ?_
      refine Eq.trans ?_ (permMat_comp_apply
        (X := fun x : (X₁.ι × X₂.ι) × X₃.ι => (X₁.X x.1.1 ≫ X₂.X x.1.2) ≫ X₃.X x.2)
        (Y := fun y : X₁.ι × (X₂.ι × X₃.ι) => X₁.X y.1 ≫ (X₂.X y.2.1 ≫ X₃.X y.2.2))
        (Equiv.prodAssoc X₁.ι X₂.ι X₃.ι)
        (fun x => (α_ (X₁.X x.1.1) (X₂.X x.1.2) (X₃.X x.2)).hom)
        (hcomp f₁ (hcomp f₂ f₃)) m _).symm
      exact hcomp₂_hcomp₂_associator _ _ _)
    (fun {a b X Y} f => by
      refine hom_ext_equiv (Equiv.punitProd Y.ι) fun m i => ?_
      rw [leftUnitor_hom, leftUnitor_hom]
      refine (comp_permMat_apply (Equiv.punitProd Y.ι) (fun x => (λ_ (Y.X x.2)).hom)
        (hcomp (𝟙 (𝟙 a)) f) m i).trans ?_
      refine Eq.trans ?_ (permMat_comp_apply (Equiv.punitProd X.ι) (fun x => (λ_ (X.X x.2)).hom)
        f m _).symm
      obtain ⟨⟨⟩, m⟩ := m
      obtain ⟨⟨⟩, i⟩ := i
      rw [hcomp_apply, CategoryTheory.Mat_.id_apply_self]
      simp only [hcomp₂, id_whiskerRight, Category.id_comp]
      exact leftUnitor_naturality _)
    (fun {a b X Y} f => by
      refine hom_ext_equiv (Equiv.prodPUnit Y.ι) fun m i => ?_
      rw [rightUnitor_hom, rightUnitor_hom]
      refine (comp_permMat_apply (Equiv.prodPUnit Y.ι) (fun x => (ρ_ (Y.X x.1)).hom)
        (hcomp f (𝟙 (𝟙 b))) m i).trans ?_
      refine Eq.trans ?_ (permMat_comp_apply (Equiv.prodPUnit X.ι) (fun x => (ρ_ (X.X x.1)).hom)
        f m _).symm
      obtain ⟨m, ⟨⟩⟩ := m
      obtain ⟨i, ⟨⟩⟩ := i
      rw [hcomp_apply, CategoryTheory.Mat_.id_apply_self]
      simp only [hcomp₂, Bicategory.whiskerLeft_id, Category.comp_id]
      exact rightUnitor_naturality _)
    (fun W X Y Z => by
      simp only [associator_hom]
      rw [id_eq_permMat' Z, id_eq_permMat' W, hcomp_permMat, hcomp_permMat,
        permMat_comp_permMat, permMat_comp_permMat, permMat_comp_permMat]
      refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
      rw [eqToHom_refl, Category.comp_id]
      simp only [hcomp₂, id_whiskerRight, Bicategory.whiskerLeft_id, Category.id_comp,
        Category.comp_id]
      exact Bicategory.pentagon _ _ _ _)
    (fun X Y => by
      simp only [associator_hom, leftUnitor_hom, rightUnitor_hom]
      rw [id_eq_permMat' X, id_eq_permMat' Y, hcomp_permMat, hcomp_permMat, permMat_comp_permMat]
      refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
      rw [eqToHom_refl, Category.comp_id]
      simp only [hcomp₂, id_whiskerRight, Bicategory.whiskerLeft_id, Category.id_comp,
        Category.comp_id]
      exact Bicategory.triangle _ _)

section Simp

variable {a b c d : MatBicat B}

theorem whiskerLeft_eq (M : a ⟶ b) {N N' : b ⟶ c} (g : N ⟶ N') : M ◁ g = hcomp (𝟙 M) g := rfl

theorem whiskerRight_eq {M M' : a ⟶ b} (f : M ⟶ M') (N : b ⟶ c) : f ▷ N = hcomp f (𝟙 N) := rfl

theorem associator_eq (M : a ⟶ b) (N : b ⟶ c) (P : c ⟶ d) : α_ M N P = associator M N P := rfl

theorem leftUnitor_eq (M : a ⟶ b) : λ_ M = leftUnitor M := rfl

theorem rightUnitor_eq (M : a ⟶ b) : ρ_ M = rightUnitor M := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whiskering of a permutation matrix is a permutation matrix. -/
theorem whiskerLeft_permMat (M : a ⟶ b) {ι κ : Type} [Fintype ι] [Fintype κ]
    {X : ι → (b.obj ⟶ c.obj)} {Y : κ → (b.obj ⟶ c.obj)} (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i)) :
    M ◁ permMat (D := b.obj ⟶ c.obj) e φ =
      permMat (X := fun x : M.ι × ι => M.X x.1 ≫ X x.2) (Y := fun y : M.ι × κ => M.X y.1 ≫ Y y.2)
        ((Equiv.refl M.ι).prodCongr e) (fun x => M.X x.1 ◁ φ x.2) := by
  rw [whiskerLeft_eq, id_eq_permMat' M, hcomp_permMat]
  exact permMat_congr (fun _ => rfl) _ _ fun x => by
    rw [eqToHom_refl, Category.comp_id]; simp [hcomp₂]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whiskering of a permutation matrix is a permutation matrix. -/
theorem permMat_whiskerRight {ι κ : Type} [Fintype ι] [Fintype κ]
    {X : ι → (a.obj ⟶ b.obj)} {Y : κ → (a.obj ⟶ b.obj)} (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i))
    (N : b ⟶ c) :
    permMat (D := a.obj ⟶ b.obj) e φ ▷ N =
      permMat (X := fun x : ι × N.ι => X x.1 ≫ N.X x.2) (Y := fun y : κ × N.ι => Y y.1 ≫ N.X y.2)
        (e.prodCongr (Equiv.refl N.ι)) (fun x => φ x.1 ▷ N.X x.2) := by
  rw [whiskerRight_eq, id_eq_permMat' N, hcomp_permMat]
  exact permMat_congr (fun _ => rfl) _ _ fun x => by
    rw [eqToHom_refl, Category.comp_id]; simp [hcomp₂]

end Simp

/-! ## Preadditive and linear structure -/

instance instPreadditiveBicategory : PreadditiveBicategory (MatBicat B) where
  whiskerLeft_add M _ _ η θ := by
    apply CategoryTheory.Mat_.hom_ext; intro x y
    simp [whiskerLeft_eq, hcomp₂, PreadditiveBicategory.whiskerLeft_add, Preadditive.comp_add]
  add_whiskerRight η θ N := by
    apply CategoryTheory.Mat_.hom_ext; intro x y
    simp [whiskerRight_eq, hcomp₂, PreadditiveBicategory.add_whiskerRight, Preadditive.add_comp]

section Linear

variable {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)] [LinearBicategory R B]

instance (a b : MatBicat B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (Mat_ (a.obj ⟶ b.obj)))

omit [PreadditiveBicategory B] [LinearBicategory R B] in
@[simp] theorem smul_apply {a b : MatBicat B} {M N : a ⟶ b} (r : R) (f : M ⟶ N) (i j) :
    (r • f) i j = r • f i j := rfl

instance instLinearBicategory : LinearBicategory R (MatBicat B) where
  whiskerLeft_smul M _ _ r η := by
    apply CategoryTheory.Mat_.hom_ext; intro x y
    simp [whiskerLeft_eq, hcomp₂, LinearBicategory.whiskerLeft_smul, Linear.comp_smul]
  smul_whiskerRight r η N := by
    apply CategoryTheory.Mat_.hom_ext; intro x y
    simp [whiskerRight_eq, hcomp₂, LinearBicategory.smul_whiskerRight, Linear.smul_comp]

end Linear

/-! ## Π-2-categories and `(Q, Π)`-2-categories -/

section Pi

variable {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)] [LinearBicategory R B]
  {a b c d : MatBicat B}

theorem associator_hom_eq (M : a ⟶ b) (N : b ⟶ c) (P : c ⟶ d) :
    (α_ M N P).hom = permMat (Equiv.prodAssoc M.ι N.ι P.ι)
      fun x => (α_ (M.X x.1.1) (N.X x.1.2) (P.X x.2)).hom := rfl

theorem associator_inv_eq (M : a ⟶ b) (N : b ⟶ c) (P : c ⟶ d) :
    (α_ M N P).inv = permMat (Equiv.prodAssoc M.ι N.ι P.ι).symm
      fun y => (α_ (M.X y.1) (N.X y.2.1) (P.X y.2.2)).inv := rfl

theorem leftUnitor_hom_eq (M : a ⟶ b) :
    (λ_ M).hom = permMat (Equiv.punitProd M.ι) fun x => (λ_ (M.X x.2)).hom := rfl

theorem leftUnitor_inv_eq (M : a ⟶ b) :
    (λ_ M).inv = permMat (Equiv.punitProd M.ι).symm fun i => (λ_ (M.X i)).inv := rfl

theorem rightUnitor_hom_eq (M : a ⟶ b) :
    (ρ_ M).hom = permMat (Equiv.prodPUnit M.ι) fun x => (ρ_ (M.X x.1)).hom := rfl

theorem rightUnitor_inv_eq (M : a ⟶ b) :
    (ρ_ M).inv = permMat (Equiv.prodPUnit M.ι).symm fun i => (ρ_ (M.X i)).inv := rfl

omit [PreadditiveBicategory B] in
theorem id₂_eq (M : a ⟶ b) : 𝟙 M = permMat (Equiv.refl M.ι) (fun i => 𝟙 (M.X i)) :=
  id_eq_permMat' M

omit [PreadditiveBicategory B] in
/-- A permutation matrix with entries `-φ i`. -/
theorem neg_permMat {ι κ : Type} [Fintype ι] [Fintype κ] {X : ι → (a.obj ⟶ b.obj)}
    {Y : κ → (a.obj ⟶ b.obj)} (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i)) :
    -permMat (D := a.obj ⟶ b.obj) e φ = permMat e (fun i => -φ i) :=
  (permMat_neg e φ).symm

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `F q ≅ q' F` of the additive envelope determined entrywise by
natural isomorphisms `F ≫ q ≅ q' ≫ F` in `B` (for `q = π`, `q'` etc.). -/
@[simps]
def braidIso {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj} (M : a ⟶ b)
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f) : M ≫ single q ≅ single q' ≫ M where
  hom := permMat (Equiv.prodComm M.ι PUnit) fun x => (e (M.X x.1)).hom
  inv := permMat (Equiv.prodComm PUnit M.ι) fun x => (e (M.X x.2)).inv
  hom_inv_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.hom_inv_id _
  inv_hom_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.inv_hom_id _

/-- The naturality of `braidIso` with respect to 2-morphisms, from the naturality in `B`. -/
theorem braidIso_naturality {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj}
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom)
    {M N : a ⟶ b} (η : M ⟶ N) :
    (braidIso M e).hom ≫ single q' ◁ η = η ▷ single q ≫ (braidIso N e).hom := by
  refine hom_ext_equiv (Equiv.prodComm N.ι PUnit) fun m i => ?_
  rw [braidIso_hom, braidIso_hom]
  refine (permMat_comp_apply (X := fun x : M.ι × PUnit => M.X x.1 ≫ q)
    (Y := fun y : PUnit × M.ι => q' ≫ M.X y.2) (Equiv.prodComm M.ι PUnit)
    (fun x => (e (M.X x.1)).hom) (single q' ◁ η) m _).trans ?_
  refine Eq.trans ?_ (comp_permMat_apply (X := fun x : N.ι × PUnit => N.X x.1 ≫ q)
    (Y := fun y : PUnit × N.ι => q' ≫ N.X y.2) (Equiv.prodComm N.ι PUnit)
    (fun x => (e (N.X x.1)).hom) (η ▷ single q) m i).symm
  obtain ⟨m, ⟨⟩⟩ := m
  obtain ⟨i, ⟨⟩⟩ := i
  rw [whiskerLeft_eq, whiskerRight_eq, hcomp_apply, hcomp_apply]
  change (e (M.X m)).hom ≫ hcomp₂ ((𝟙 (single q')) PUnit.unit PUnit.unit) (η m i) =
    hcomp₂ (η m i) ((𝟙 (single q)) PUnit.unit PUnit.unit) ≫ (e (N.X i)).hom
  rw [id_apply_self, id_apply_self]
  simp only [hcomp₂, id_whiskerRight, Category.id_comp, Bicategory.whiskerLeft_id,
    Category.comp_id]
  exact he (η m i)

/-- The isomorphism `single q ≫ single q' ≅ 𝟙 a` determined by `q ≫ q' ≅ 𝟙`. -/
@[simps]
def unitIso {q q' : a.obj ⟶ a.obj} (e : q ≫ q' ≅ 𝟙 a.obj) : single q ≫ single q' ≅ 𝟙 a where
  hom := permMat (Equiv.punitProd PUnit) fun _ => e.hom
  inv := permMat (Equiv.punitProd PUnit).symm fun _ => e.inv
  hom_inv_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.hom_inv_id _
  inv_hom_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.inv_hom_id _

variable [PiTwoCategory R B]

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝛏" => PiTwoCategory.ξ (R := R)

set_option backward.isDefEq.respectTransparency false in
/-- **Brundan–Ellis, §6.** The additive envelope of a Π-2-category is a Π-2-category, with
`π_λ` the one-by-one matrix and `β`, `ξ` extended entrywise. -/
instance instPiTwoCategory : PiTwoCategory R (MatBicat B) where
  pi a := single (𝛑 a.obj)
  β M := braidIso M 𝛃
  β_naturality η := braidIso_naturality 𝛃 (fun η => PiTwoCategory.β_naturality η) η
  β_comp M N := by
    simp only [braidIso_hom, associator_hom_eq, associator_inv_eq, whiskerLeft_permMat,
      permMat_whiskerRight]
    repeat rw [permMat_comp_permMat]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact PiTwoCategory.β_comp (R := R) (M.X x.1.1) (N.X x.1.2)
  β_id a := by
    rw [braidIso_hom, leftUnitor_hom_eq, rightUnitor_inv_eq, permMat_comp_permMat]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact PiTwoCategory.β_id (R := R) a.obj
  β_pi a := by
    rw [braidIso_hom, id₂_eq, neg_permMat]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact PiTwoCategory.β_pi (R := R) a.obj
  ξ a := unitIso (𝛏 a.obj)
  ξ_comm M := by
    simp only [braidIso_hom, unitIso_hom, unitIso_inv, associator_hom_eq, associator_inv_eq,
      leftUnitor_inv_eq, rightUnitor_hom_eq, whiskerLeft_permMat, permMat_whiskerRight]
    repeat rw [permMat_comp_permMat]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact PiTwoCategory.ξ_comm (R := R) (M.X x.1)

@[simp] theorem pi_eq (a : MatBicat B) : 𝛑 a = single (𝛑 a.obj) := rfl

theorem β_hom_eq (M : a ⟶ b) :
    (𝛃 M).hom = permMat (Equiv.prodComm M.ι PUnit) fun x => (𝛃 (M.X x.1)).hom := rfl

theorem β_inv_eq (M : a ⟶ b) :
    (𝛃 M).inv = permMat (Equiv.prodComm PUnit M.ι) fun x => (𝛃 (M.X x.2)).inv := rfl

theorem ξ_hom_eq (a : MatBicat B) :
    (𝛏 a).hom = permMat (Equiv.punitProd PUnit) fun _ => (𝛏 a.obj).hom := rfl

theorem ξ_inv_eq (a : MatBicat B) :
    (𝛏 a).inv = permMat (Equiv.punitProd PUnit).symm fun _ => (𝛏 a.obj).inv := rfl

end Pi

section QPi

variable {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)] [LinearBicategory R B]
  [QPiTwoCategory R B] {a b c d : MatBicat B}

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝐪" => QPiTwoCategory.q (R := R)
local notation "𝐪⁻¹" => QPiTwoCategory.qinv (R := R)
local notation "𝛄" => QPiTwoCategory.γ (R := R)

set_option backward.isDefEq.respectTransparency false in
/-- **Brundan–Ellis, §6.** The additive envelope of a `(Q, Π)`-2-category is a
`(Q, Π)`-2-category, with `q_λ`, `q_λ⁻¹` the one-by-one matrices and `γ`, `ii`, `jj`
extended entrywise. -/
instance instQPiTwoCategory : QPiTwoCategory R (MatBicat B) where
  q a := single (𝐪 a.obj)
  qinv a := single (𝐪⁻¹ a.obj)
  γ M := braidIso M 𝛄
  γ_naturality η := braidIso_naturality 𝛄 (fun η => QPiTwoCategory.γ_naturality η) η
  γ_comp M N := by
    simp only [braidIso_hom, associator_hom_eq, associator_inv_eq, whiskerLeft_permMat,
      permMat_whiskerRight]
    repeat rw [permMat_comp_permMat]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact QPiTwoCategory.γ_comp (R := R) (M.X x.1.1) (N.X x.1.2)
  γ_id a := by
    rw [braidIso_hom, leftUnitor_hom_eq, rightUnitor_inv_eq, permMat_comp_permMat]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact QPiTwoCategory.γ_id (R := R) a.obj
  γ_q a := by
    rw [braidIso_hom, id₂_eq]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact QPiTwoCategory.γ_q (R := R) a.obj
  γ_pi a := by
    rw [braidIso_hom, β_inv_eq]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact QPiTwoCategory.γ_pi (R := R) a.obj
  ii a := unitIso (QPiTwoCategory.ii (R := R) a.obj)
  jj a := unitIso (QPiTwoCategory.jj (R := R) a.obj)
  q_ii a := by
    simp only [unitIso_hom, associator_hom_eq, leftUnitor_hom_eq, rightUnitor_hom_eq,
      whiskerLeft_permMat, permMat_whiskerRight]
    repeat rw [permMat_comp_permMat]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact QPiTwoCategory.q_ii (R := R) a.obj
  ii_qinv a := by
    simp only [unitIso_hom, associator_inv_eq, leftUnitor_hom_eq, rightUnitor_hom_eq,
      whiskerLeft_permMat, permMat_whiskerRight]
    repeat rw [permMat_comp_permMat]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact QPiTwoCategory.ii_qinv (R := R) a.obj

@[simp] theorem q_eq (a : MatBicat B) : 𝐪 a = single (𝐪 a.obj) := rfl

@[simp] theorem qinv_eq (a : MatBicat B) : 𝐪⁻¹ a = single (𝐪⁻¹ a.obj) := rfl

theorem γ_hom_eq (M : a ⟶ b) :
    (𝛄 M).hom = permMat (Equiv.prodComm M.ι PUnit) fun x => (𝛄 (M.X x.1)).hom := rfl

theorem γ_inv_eq (M : a ⟶ b) :
    (𝛄 M).inv = permMat (Equiv.prodComm PUnit M.ι) fun x => (𝛄 (M.X x.2)).inv := rfl

theorem ii_hom_eq (a : MatBicat B) :
    (QPiTwoCategory.ii (R := R) a).hom =
      permMat (Equiv.punitProd PUnit) fun _ => (QPiTwoCategory.ii (R := R) a.obj).hom := rfl

theorem jj_hom_eq (a : MatBicat B) :
    (QPiTwoCategory.jj (R := R) a).hom =
      permMat (Equiv.punitProd PUnit) fun _ => (QPiTwoCategory.jj (R := R) a.obj).hom := rfl

end QPi

end MatBicat

end StringDiagrams

end
