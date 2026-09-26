import StringDiagrams.Super.Envelope
import StringDiagrams.Super.Monoidal

/-!
# The Π-envelope of a monoidal supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.16: for a monoidal supercategory `A`, the Π-envelope `A_π` is a monoidal
supercategory with `(Πᵃ λ) ⊗ (Πᵇ μ) := Π^{a+b}(λ ⊗ μ)`, unit `Π⁰ 1`, coherence maps induced from
those of `A`, and tensor product of morphisms

  `f_a^b ⊗ g_c^d := (-1)^{a|g| + |f|d + ad + ac} (f ⊗ g)_{a+c}^{b+d}`.

In the whiskering presentation of `StringDiagrams.MonoidalSupercategory`, this amounts to
`Πᵃ λ ◁ g_c^d = (-1)^{a|g_c^d|} (λ ◁ g)_{a+c}^{a+d}` and
`f_a^b ▷ Πᶜ μ = (-1)^{|f|c} (f ▷ μ)_{a+c}^{b+c}` (`toHom_whiskerLeft_of_mem`,
`toHom_whiskerRight_of_mem`), and the paper's formula for the tensor product is
`toHom_superTensorHom`.

## Main statements

* `Envelope.instMonoidalCategoryStruct`, `Envelope.monoidalSupercategory`: Definition 1.16.
* `Envelope.toHom_superTensorHom`: the sign formula of Definition 1.16 for the paper's tensor
  product `superTensorHom`.
* `Envelope.piUnit`, `Envelope.ζUnit`: the object `π := Π¹ 1` and the odd isomorphism
  `ζ := (1_1)_1^0 : π ≅ 1` (Definition 1.16), making `A_π` a monoidal Π-supercategory in the
  sense of Definition 1.12 (see `StringDiagrams.Super.MonoidalPi`).
* `Envelope.monoidalJ`: the canonical superfunctor `J : A → A_π` is a (strict) monoidal
  superfunctor.

Along the way we record, for any monoidal supercategory, the naturality of the associator in
each variable separately (`MonoidalSupercategory.associator_naturality_left` etc.) and the
converse statement used to check associator naturality in `A_π`
(`MonoidalSupercategory.associator_naturality_of_whiskers`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w w₁ w₂

namespace MonoidalSupercategory

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]

variable (R) in
include R in
theorem associator_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    (f ▷ Y) ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) := by
  have h := associator_naturality (R := R) f (𝟙 Y) (𝟙 Z)
  rwa [tensor_id R, tensorHom_def (R := R) (f ⊗ 𝟙 Y), tensorHom_def (R := R) f,
    tensorHom_def (R := R) f, whiskerLeft_id (R := R), whiskerLeft_id (R := R),
    whiskerLeft_id (R := R), Category.comp_id, Category.comp_id, Category.comp_id] at h

variable (R) in
include R in
theorem associator_naturality_middle (X : C) {Y Y' : C} (g : Y ⟶ Y') (Z : C) :
    (X ◁ g) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ (g ▷ Z) := by
  have h := associator_naturality (R := R) (𝟙 X) g (𝟙 Z)
  rwa [tensorHom_def (R := R) (𝟙 X ⊗ g), tensorHom_def (R := R) (𝟙 X) g,
    tensorHom_def (R := R) (𝟙 X), tensorHom_def (R := R) g, id_whiskerRight (R := R),
    id_whiskerRight (R := R), whiskerLeft_id (R := R), whiskerLeft_id (R := R),
    Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id] at h

variable (R) in
include R in
theorem associator_naturality_right (X Y : C) {Z Z' : C} (h : Z ⟶ Z') :
    (X ⊗ Y) ◁ h ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ (Y ◁ h) := by
  have e := associator_naturality (R := R) (𝟙 X) (𝟙 Y) h
  rwa [tensor_id R, tensorHom_def (R := R) (𝟙 (X ⊗ Y)), tensorHom_def (R := R) (𝟙 X),
    tensorHom_def (R := R) (𝟙 Y), id_whiskerRight (R := R), id_whiskerRight (R := R),
    id_whiskerRight (R := R), Category.id_comp, Category.id_comp, Category.id_comp] at e

end MonoidalSupercategory

/-- Associator naturality from naturality in each variable separately, for any monoidal
structure whose whiskerings are functorial and whose tensor product of morphisms is
`f ▷ _ ≫ _ ◁ g`. -/
theorem MonoidalSupercategory.associator_naturality_of_whiskers {C : Type w₁} [Category.{w₂} C]
    [MonoidalCategoryStruct C]
    (tensorHom_def : ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      f ⊗ g = f ▷ X₂ ≫ Y₁ ◁ g)
    (whiskerLeft_comp : ∀ (X : C) {Y Z W : C} (f : Y ⟶ Z) (g : Z ⟶ W),
      X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g)
    (comp_whiskerRight : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (W : C),
      (f ≫ g) ▷ W = f ▷ W ≫ g ▷ W)
    (left : ∀ {X X' : C} (f : X ⟶ X') (Y Z : C),
      (f ▷ Y) ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z))
    (middle : ∀ (X : C) {Y Y' : C} (g : Y ⟶ Y') (Z : C),
      (X ◁ g) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ (g ▷ Z))
    (right : ∀ (X Y : C) {Z Z' : C} (h : Z ⟶ Z'),
      (X ⊗ Y) ◁ h ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ (Y ◁ h))
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ (f₂ ⊗ f₃)) := by
  rw [tensorHom_def (f₁ ⊗ f₂), tensorHom_def f₁ f₂, tensorHom_def f₁, tensorHom_def f₂,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc, Category.assoc, right,
    ← Category.assoc ((Y₁ ◁ f₂) ▷ X₃), middle, Category.assoc, ← Category.assoc ((f₁ ▷ X₂) ▷ X₃),
    left, Category.assoc]

namespace Envelope

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C]

omit [CommRing R] in
/-- Induction on morphisms of the envelope via morphisms homogeneous in `C`. -/
@[elab_as_elim]
theorem induction_on' [CommRing R] [Linear R C] [Supercategory R C] {X Y : Envelope R C}
    {P : (X ⟶ Y) → Prop} (f : X ⟶ Y) (zero : P 0)
    (hom : ∀ (r : ZMod 2) (g : X ⟶ Y), toHom g ∈ parity (R := R) X.obj Y.obj r → P g)
    (add : ∀ g h, P g → P h → P (g + h)) : P f :=
  induction_on (R := R) (P := fun g : X.obj ⟶ Y.obj => P (ofHom g)) (toHom f) zero
    (fun r g hg => hom r (ofHom g) hg) (fun g h => add (ofHom g) (ofHom h))

variable [MonoidalCategoryStruct C]

/-- **Definition 1.16.** The monoidal structure on the Π-envelope:
`Πᵃ λ ⊗ Πᵇ μ = Π^{a+b}(λ ⊗ μ)`, unit `Π⁰ 1`, `Πᵃ λ ◁ g = λ ◁ g'` where `g'` is the twist of
`g` by `a` in `A_π`, and `f ▷ Πᶜ μ = f'' ▷ μ` where `f''` is the twist of `f` by `c` in `A`;
coherence maps are those of `A`. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Envelope R C) where
  tensorObj X Y := ⟨X.par + Y.par, X.obj ⊗ Y.obj⟩
  whiskerLeft X _ _ g := ofHom (X.obj ◁ toHom (twist R X.par g))
  whiskerRight {_ _} f Y := ofHom (twist R Y.par (toHom f) ▷ Y.obj)
  tensorHom {_ Y₁ X₂ _} f g :=
    ofHom (twist R X₂.par (toHom f) ▷ X₂.obj ≫ Y₁.obj ◁ toHom (twist R Y₁.par g))
  tensorUnit := ⟨0, 𝟙_ C⟩
  associator X Y Z := isoOfIso (α_ X.obj Y.obj Z.obj)
  leftUnitor X := isoOfIso (λ_ X.obj)
  rightUnitor X := isoOfIso (ρ_ X.obj)

@[simp] theorem tensorObj_par (X Y : Envelope R C) : (X ⊗ Y).par = X.par + Y.par := rfl

@[simp] theorem tensorObj_obj (X Y : Envelope R C) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

@[simp] theorem tensorUnit_par : (𝟙_ (Envelope R C)).par = 0 := rfl

@[simp] theorem tensorUnit_obj : (𝟙_ (Envelope R C)).obj = 𝟙_ C := rfl

theorem toHom_whiskerLeft (X : Envelope R C) {Y Y' : Envelope R C} (g : Y ⟶ Y') :
    toHom (X ◁ g) = X.obj ◁ toHom (twist R X.par g) := rfl

theorem toHom_whiskerRight {X X' : Envelope R C} (f : X ⟶ X') (Y : Envelope R C) :
    toHom (f ▷ Y) = twist R Y.par (toHom f) ▷ Y.obj := rfl

theorem tensorHom_def' {X₁ Y₁ X₂ Y₂ : Envelope R C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ g = f ▷ X₂ ≫ Y₁ ◁ g := rfl

@[simp] theorem toHom_associator_hom (X Y Z : Envelope R C) :
    toHom (α_ X Y Z).hom = (α_ X.obj Y.obj Z.obj).hom := rfl

@[simp] theorem toHom_associator_inv (X Y Z : Envelope R C) :
    toHom (α_ X Y Z).inv = (α_ X.obj Y.obj Z.obj).inv := rfl

@[simp] theorem toHom_leftUnitor_hom (X : Envelope R C) :
    toHom (λ_ X).hom = (λ_ X.obj).hom := rfl

@[simp] theorem toHom_leftUnitor_inv (X : Envelope R C) :
    toHom (λ_ X).inv = (λ_ X.obj).inv := rfl

@[simp] theorem toHom_rightUnitor_hom (X : Envelope R C) :
    toHom (ρ_ X).hom = (ρ_ X.obj).hom := rfl

@[simp] theorem toHom_rightUnitor_inv (X : Envelope R C) :
    toHom (ρ_ X).inv = (ρ_ X.obj).inv := rfl

variable [MonoidalSupercategory R C]

/-- `Πᵃ λ ◁ g = (-1)^{a|g|} (λ ◁ g)` for `g : Πᶜ μ ⟶ Πᵈ ν` of parity `r` in `A` (so of
parity `r + c + d` in `A_π`). -/
theorem toHom_whiskerLeft_of_mem (X : Envelope R C) {Y Y' : Envelope R C} {g : Y ⟶ Y'}
    {r : ZMod 2} (hg : toHom g ∈ parity (R := R) Y.obj Y'.obj r) :
    toHom (X ◁ g) = sign R (X.par * (r + (Y.par + Y'.par))) • (X.obj ◁ toHom g) := by
  rw [toHom_whiskerLeft, toHom_twist, twist_of_mem _ hg, smul_smul, ← sign_add,
    MonoidalSupercategory.whiskerLeft_smul]
  congr 2
  ring

/-- `f ▷ Πᶜ μ = (-1)^{|f|c} (f ▷ μ)` for `f` of parity `r` in `A`. -/
theorem toHom_whiskerRight_of_mem {X X' : Envelope R C} {f : X ⟶ X'} {r : ZMod 2}
    (hf : toHom f ∈ parity (R := R) X.obj X'.obj r) (Y : Envelope R C) :
    toHom (f ▷ Y) = sign R (Y.par * r) • (toHom f ▷ Y.obj) := by
  rw [toHom_whiskerRight, twist_of_mem _ hf, MonoidalSupercategory.smul_whiskerRight]

theorem toHom_whiskerLeft_mem (X : Envelope R C) {Y Y' : Envelope R C} {g : Y ⟶ Y'}
    {r : ZMod 2} (hg : toHom g ∈ parity (R := R) Y.obj Y'.obj r) :
    toHom (X ◁ g) ∈ parity (R := R) (X.obj ⊗ Y.obj) (X.obj ⊗ Y'.obj) r := by
  rw [toHom_whiskerLeft_of_mem X hg]
  exact Submodule.smul_mem _ _ (MonoidalSupercategory.whiskerLeft_mem _ hg)

theorem toHom_whiskerRight_mem {X X' : Envelope R C} {f : X ⟶ X'} {r : ZMod 2}
    (hf : toHom f ∈ parity (R := R) X.obj X'.obj r) (Y : Envelope R C) :
    toHom (f ▷ Y) ∈ parity (R := R) (X.obj ⊗ Y.obj) (X'.obj ⊗ Y.obj) r := by
  rw [toHom_whiskerRight_of_mem hf]
  exact Submodule.smul_mem _ _ (MonoidalSupercategory.whiskerRight_mem _ hf)

omit [MonoidalSupercategory R C] in
/-- Whiskering by an object of parity shift `0`. -/
theorem toHom_whiskerLeft_of_par_zero (X : Envelope R C) (hX : X.par = 0) {Y Y' : Envelope R C}
    (g : Y ⟶ Y') : toHom (X ◁ g) = X.obj ◁ toHom g := by
  rw [toHom_whiskerLeft, hX, twist_zero]

omit [MonoidalSupercategory R C] in
theorem toHom_whiskerRight_of_par_zero {X X' : Envelope R C} (f : X ⟶ X') (Y : Envelope R C)
    (hY : Y.par = 0) : toHom (f ▷ Y) = toHom f ▷ Y.obj := by
  rw [toHom_whiskerRight, hY, twist_zero]

/-- Whiskering a morphism that is even both in `A` and in `A_π`. -/
theorem toHom_whiskerLeft_of_even (X : Envelope R C) {Y Y' : Envelope R C} {g : Y ⟶ Y'}
    (hg : toHom g ∈ parity (R := R) Y.obj Y'.obj 0) (hY : Y.par = Y'.par) :
    toHom (X ◁ g) = X.obj ◁ toHom g := by
  rw [toHom_whiskerLeft_of_mem X hg, hY, zmod2_add_self, add_zero, mul_zero, sign_zero, one_smul]

theorem toHom_whiskerRight_of_even {X X' : Envelope R C} {f : X ⟶ X'}
    (hf : toHom f ∈ parity (R := R) X.obj X'.obj 0) (Y : Envelope R C) :
    toHom (f ▷ Y) = toHom f ▷ Y.obj := by
  rw [toHom_whiskerRight_of_mem hf, mul_zero, sign_zero, one_smul]

theorem whiskerLeft_add' (X : Envelope R C) {Y Y' : Envelope R C} (f g : Y ⟶ Y') :
    X ◁ (f + g) = X ◁ f + X ◁ g := by
  apply hom_ext
  rw [toHom_add, toHom_whiskerLeft, toHom_whiskerLeft, toHom_whiskerLeft, map_add, toHom_add,
    MonoidalSupercategory.whiskerLeft_add (R := R)]

theorem add_whiskerRight' {X X' : Envelope R C} (f g : X ⟶ X') (Y : Envelope R C) :
    (f + g) ▷ Y = f ▷ Y + g ▷ Y := by
  apply hom_ext
  rw [toHom_add, toHom_whiskerRight, toHom_whiskerRight, toHom_whiskerRight, toHom_add, map_add,
    MonoidalSupercategory.add_whiskerRight (R := R)]

theorem whiskerLeft_zero' (X : Envelope R C) {Y Y' : Envelope R C} :
    X ◁ (0 : Y ⟶ Y') = 0 := by
  apply hom_ext
  rw [toHom_whiskerLeft, map_zero, toHom_zero, MonoidalSupercategory.whiskerLeft_zero R]; rfl

theorem zero_whiskerRight' {X X' : Envelope R C} (Y : Envelope R C) :
    (0 : X ⟶ X') ▷ Y = 0 := by
  apply hom_ext
  rw [toHom_whiskerRight, toHom_zero, map_zero, MonoidalSupercategory.zero_whiskerRight R]; rfl

theorem associator_naturality_left' {X X' : Envelope R C} (f : X ⟶ X') (Y Z : Envelope R C) :
    (f ▷ Y) ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) := by
  refine induction_on' (R := R) f ?_ (fun r f hf => ?_) (fun f g hf hg => ?_)
  · rw [zero_whiskerRight', zero_whiskerRight', zero_whiskerRight', Limits.zero_comp,
      Limits.comp_zero]
  · apply hom_ext
    rw [toHom_comp, toHom_comp, toHom_whiskerRight_of_mem (toHom_whiskerRight_mem hf Y),
      toHom_whiskerRight_of_mem hf, toHom_whiskerRight_of_mem hf,
      MonoidalSupercategory.smul_whiskerRight, smul_smul, Linear.smul_comp, Linear.comp_smul,
      toHom_associator_hom, toHom_associator_hom,
      MonoidalSupercategory.associator_naturality_left R, ← sign_add]
    congr 2
    simp only [tensorObj_par]
    ring
  · rw [add_whiskerRight', add_whiskerRight', add_whiskerRight', Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]

theorem associator_naturality_middle' (X : Envelope R C) {Y Y' : Envelope R C} (g : Y ⟶ Y')
    (Z : Envelope R C) :
    (X ◁ g) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ (g ▷ Z) := by
  refine induction_on' (R := R) g ?_ (fun r g hg => ?_) (fun f g hf hg => ?_)
  · rw [whiskerLeft_zero', zero_whiskerRight', zero_whiskerRight', whiskerLeft_zero',
      Limits.zero_comp, Limits.comp_zero]
  · apply hom_ext
    rw [toHom_comp, toHom_comp, toHom_whiskerRight_of_mem (toHom_whiskerLeft_mem X hg),
      toHom_whiskerLeft_of_mem X hg, toHom_whiskerLeft_of_mem X (toHom_whiskerRight_mem hg Z),
      toHom_whiskerRight_of_mem hg, MonoidalSupercategory.smul_whiskerRight,
      MonoidalSupercategory.whiskerLeft_smul, smul_smul, smul_smul, Linear.smul_comp,
      Linear.comp_smul, toHom_associator_hom, toHom_associator_hom,
      ← sign_add, ← sign_add]
    erw [MonoidalSupercategory.associator_naturality_middle R]
    congr 2
    simp only [tensorObj_par]
    clear hg
    generalize X.par = a; generalize Y.par = b; generalize Y'.par = c; generalize Z.par = d
    revert a b c d r; decide
  · rw [whiskerLeft_add', add_whiskerRight', add_whiskerRight', whiskerLeft_add',
      Preadditive.add_comp, Preadditive.comp_add, hf, hg]

theorem associator_naturality_right' (X Y : Envelope R C) {Z Z' : Envelope R C} (h : Z ⟶ Z') :
    (X ⊗ Y) ◁ h ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ (Y ◁ h) := by
  refine induction_on' (R := R) h ?_ (fun r h hh => ?_) (fun f g hf hg => ?_)
  · rw [whiskerLeft_zero', whiskerLeft_zero', whiskerLeft_zero', Limits.zero_comp,
      Limits.comp_zero]
  · apply hom_ext
    rw [toHom_comp, toHom_comp, toHom_whiskerLeft_of_mem _ hh,
      toHom_whiskerLeft_of_mem X (toHom_whiskerLeft_mem Y hh), toHom_whiskerLeft_of_mem Y hh,
      MonoidalSupercategory.whiskerLeft_smul, smul_smul, Linear.smul_comp, Linear.comp_smul,
      toHom_associator_hom, toHom_associator_hom, ← sign_add]
    erw [MonoidalSupercategory.associator_naturality_right R]
    congr 2
    simp only [tensorObj_par]
    clear hh
    generalize X.par = a; generalize Y.par = b; generalize Z.par = c; generalize Z'.par = d
    revert a b c d r; decide
  · rw [whiskerLeft_add', whiskerLeft_add', whiskerLeft_add', Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]

/-- **Definition 1.16.** The Π-envelope of a monoidal supercategory is a monoidal
supercategory. -/
instance monoidalSupercategory : MonoidalSupercategory R (Envelope R C) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id X Y := by
    apply hom_ext; rw [toHom_whiskerLeft, twist_id]
    exact MonoidalSupercategory.whiskerLeft_id (R := R) _ _
  id_whiskerRight X Y := by
    apply hom_ext; rw [toHom_whiskerRight, toHom_id, twist_id]
    exact MonoidalSupercategory.id_whiskerRight (R := R) _ _
  whiskerLeft_comp X _ _ _ f g := by
    apply hom_ext
    rw [toHom_comp, toHom_whiskerLeft, toHom_whiskerLeft, toHom_whiskerLeft, twist_comp,
      toHom_comp, MonoidalSupercategory.whiskerLeft_comp (R := R)]
  comp_whiskerRight f g W := by
    apply hom_ext
    rw [toHom_comp, toHom_whiskerRight, toHom_whiskerRight, toHom_whiskerRight, toHom_comp,
      twist_comp, MonoidalSupercategory.comp_whiskerRight (R := R)]
  whiskerLeft_add X _ _ f g := whiskerLeft_add' X f g
  add_whiskerRight f g Z := add_whiskerRight' f g Z
  whiskerLeft_smul X _ _ r f := by
    apply hom_ext
    rw [toHom_smul, toHom_whiskerLeft, toHom_whiskerLeft, map_smul, toHom_smul,
      MonoidalSupercategory.whiskerLeft_smul]
  smul_whiskerRight r f Z := by
    apply hom_ext
    rw [toHom_smul, toHom_whiskerRight, toHom_whiskerRight, toHom_smul, map_smul,
      MonoidalSupercategory.smul_whiskerRight]
  whiskerLeft_mem X Y Z p f hf := by
    rw [mem_parity_iff] at hf ⊢
    have := toHom_whiskerLeft_mem X hf
    convert this using 2
    simp only [tensorObj_par]
    generalize X.par = a; generalize Y.par = b; generalize Z.par = c
    clear hf this; revert a b c p; decide
  whiskerRight_mem {X Y p f} Z hf := by
    rw [mem_parity_iff] at hf ⊢
    have := toHom_whiskerRight_mem hf Z
    convert this using 2
    simp only [tensorObj_par]
    generalize X.par = a; generalize Y.par = b; generalize Z.par = c
    clear hf this; revert a b c p; decide
  super_interchange {X X' Y Y' p q f g} hf hg := by
    rw [mem_parity_iff] at hf hg
    rw [koszulSign_smul (R := R)]
    apply hom_ext
    rw [toHom_comp, toHom_smul, toHom_comp, toHom_whiskerRight_of_mem hf,
      toHom_whiskerLeft_of_mem _ hg, toHom_whiskerLeft_of_mem _ hg,
      toHom_whiskerRight_of_mem hf, Linear.smul_comp, Linear.comp_smul, Linear.smul_comp,
      Linear.comp_smul, MonoidalSupercategory.super_interchange hf hg,
      koszulSign_smul (R := R), smul_smul, smul_smul, smul_smul, smul_smul, ← sign_add,
      ← sign_add, ← sign_add, ← sign_add]
    congr 2
    clear hf hg
    generalize X.par = a; generalize X'.par = b; generalize Y.par = c; generalize Y'.par = d
    revert a b c d p q; decide
  associator_naturality f₁ f₂ f₃ :=
    MonoidalSupercategory.associator_naturality_of_whiskers (fun _ _ => rfl)
      (fun X _ _ _ f g => by
        apply hom_ext
        rw [toHom_comp, toHom_whiskerLeft, toHom_whiskerLeft, toHom_whiskerLeft, twist_comp,
          toHom_comp, MonoidalSupercategory.whiskerLeft_comp (R := R)])
      (fun f g W => by
        apply hom_ext
        rw [toHom_comp, toHom_whiskerRight, toHom_whiskerRight, toHom_whiskerRight, toHom_comp,
          twist_comp, MonoidalSupercategory.comp_whiskerRight (R := R)])
      associator_naturality_left' associator_naturality_middle' associator_naturality_right'
      f₁ f₂ f₃
  leftUnitor_naturality f := by
    apply hom_ext
    rw [toHom_comp, toHom_comp, toHom_whiskerLeft_of_par_zero _ rfl, toHom_leftUnitor_hom,
      toHom_leftUnitor_hom]
    exact MonoidalSupercategory.leftUnitor_naturality (R := R) _
  rightUnitor_naturality f := by
    apply hom_ext
    rw [toHom_comp, toHom_comp, toHom_whiskerRight_of_par_zero _ _ rfl, toHom_rightUnitor_hom,
      toHom_rightUnitor_hom]
    exact MonoidalSupercategory.rightUnitor_naturality (R := R) _
  pentagon W X Y Z := by
    apply hom_ext
    simp only [toHom_comp, toHom_associator_hom]
    rw [toHom_whiskerRight_of_even (MonoidalSupercategory.associator_hom_mem _ _ _),
      toHom_whiskerLeft_of_even _ (MonoidalSupercategory.associator_hom_mem _ _ _)
        (by simp only [tensorObj_par, add_assoc]), toHom_associator_hom, toHom_associator_hom]
    exact MonoidalSupercategory.pentagon (R := R) _ _ _ _
  triangle X Y := by
    apply hom_ext
    simp only [toHom_comp, toHom_associator_hom]
    rw [toHom_whiskerRight_of_even (MonoidalSupercategory.rightUnitor_hom_mem _),
      toHom_whiskerLeft_of_even _ (MonoidalSupercategory.leftUnitor_hom_mem _)
        (by simp only [tensorObj_par, tensorUnit_par, zero_add]), toHom_leftUnitor_hom,
      toHom_rightUnitor_hom]
    exact MonoidalSupercategory.triangle (R := R) _ _
  associator_hom_mem X Y Z := by
    rw [mem_parity_iff, toHom_associator_hom]
    convert MonoidalSupercategory.associator_hom_mem (R := R) X.obj Y.obj Z.obj using 2
    simp only [tensorObj_par]; generalize X.par = a; generalize Y.par = b
    generalize Z.par = c; revert a b c; decide
  leftUnitor_hom_mem X := by
    rw [mem_parity_iff, toHom_leftUnitor_hom]
    convert MonoidalSupercategory.leftUnitor_hom_mem (R := R) X.obj using 2
    simp only [tensorObj_par, tensorUnit_par, zero_add, zmod2_add_self]
  rightUnitor_hom_mem X := by
    rw [mem_parity_iff, toHom_rightUnitor_hom]
    convert MonoidalSupercategory.rightUnitor_hom_mem (R := R) X.obj using 2
    simp only [tensorObj_par, tensorUnit_par, add_zero, zmod2_add_self]

/-- **Definition 1.16**, the sign formula: for `f : Πᵃ λ ⟶ Πᵇ μ` and `g : Πᶜ ν ⟶ Πᵈ ρ`
homogeneous (in `A`) of parities `|f|`, `|g|`, the paper's tensor product is
`f_a^b ⊗ g_c^d = (-1)^{a|g| + |f|d + ad + ac} (f ⊗ g)_{a+c}^{b+d}`. -/
theorem toHom_superTensorHom {X X' Y Y' : Envelope R C} {f : X ⟶ X'} {g : Y ⟶ Y'}
    {pf pg : ZMod 2} (hf : toHom f ∈ parity (R := R) X.obj X'.obj pf)
    (hg : toHom g ∈ parity (R := R) Y.obj Y'.obj pg) :
    toHom (MonoidalSupercategory.superTensorHom f g) =
      sign R (X.par * pg + pf * Y'.par + X.par * Y'.par + X.par * Y.par) •
        MonoidalSupercategory.superTensorHom (toHom f) (toHom g) := by
  rw [MonoidalSupercategory.superTensorHom, MonoidalSupercategory.superTensorHom, toHom_comp,
    toHom_whiskerLeft_of_mem X hg, toHom_whiskerRight_of_mem hf, Linear.smul_comp,
    Linear.comp_smul, smul_smul, ← sign_add]
  congr 2
  ring

/-! ## The monoidal Π-structure and the monoidal superfunctor `J` -/

variable (R C) in
/-- The object `π := Π¹ 1` of the monoidal Π-envelope (Definition 1.16). -/
def piUnit : Envelope R C := ⟨1, 𝟙_ C⟩

/-- The odd isomorphism `ζ := (1_1)_1^0 : π ≅ 1` (Definition 1.16). -/
def ζUnit : piUnit R C ≅ 𝟙_ (Envelope R C) := isoOfIso (Iso.refl (𝟙_ C))

omit [MonoidalSupercategory R C] in
theorem ζUnit_hom_mem : (ζUnit (R := R) (C := C)).hom ∈ parity (R := R) _ _ 1 := by
  rw [mem_parity_iff]
  show 𝟙 (𝟙_ C) ∈ parity (R := R) (𝟙_ C) (𝟙_ C) (1 + (1 + 0))
  exact id_mem _

/-- The canonical superfunctor `J : A ⥤ A_π` is a (strict) monoidal superfunctor. -/
def monoidalJ : MonoidalSuperfunctor R (J R C) where
  μIso X Y := isoOfIso (Iso.refl (X ⊗ Y))
  εIso := Iso.refl _
  μ_mem X Y := by
    rw [mem_parity_iff]
    convert id_mem (R := R) (MonoidalCategoryStruct.tensorObj X Y) using 2
  ε_mem := id_mem _
  μ_natural_left f X' := by
    apply hom_ext
    simp only [toHom_comp, isoOfIso_hom, Iso.refl_hom, toHom_ofHom, Category.comp_id,
      Category.id_comp]
    rw [toHom_whiskerRight_of_par_zero _ _ rfl]; simp
  μ_natural_right X' f := by
    apply hom_ext
    simp only [toHom_comp, isoOfIso_hom, Iso.refl_hom, toHom_ofHom, Category.comp_id,
      Category.id_comp]
    rw [toHom_whiskerLeft_of_par_zero _ rfl]; simp
  associativity X Y Z := by
    apply hom_ext
    simp only [toHom_comp, isoOfIso_hom, Iso.refl_hom, toHom_ofHom, Category.id_comp,
      J_map, toHom_associator_hom]
    rw [toHom_whiskerRight_of_par_zero _ _ rfl, toHom_whiskerLeft_of_par_zero _ rfl]
    simp [MonoidalSupercategory.id_whiskerRight (R := R),
      MonoidalSupercategory.whiskerLeft_id (R := R)]
  left_unitality X := by
    apply hom_ext
    simp only [toHom_comp, isoOfIso_hom, Iso.refl_hom, toHom_ofHom, Category.id_comp, J_map,
      toHom_leftUnitor_hom]
    rw [toHom_whiskerRight_of_par_zero _ _ rfl]
    simp [MonoidalSupercategory.id_whiskerRight (R := R)]
  right_unitality X := by
    apply hom_ext
    simp only [toHom_comp, isoOfIso_hom, Iso.refl_hom, toHom_ofHom, Category.id_comp, J_map,
      toHom_rightUnitor_hom]
    rw [toHom_whiskerLeft_of_par_zero _ rfl]
    simp [MonoidalSupercategory.whiskerLeft_id (R := R)]

end Envelope

end StringDiagrams

end
